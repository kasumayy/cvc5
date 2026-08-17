/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arithmetic theory.
 */

#include "theory/arith/theory_arith.h"
#include <vector>

#include "cvc5/cvc5_proof_rule.h"
#include "options/smt_options.h"
#include "printer/smt2/smt2_printer.h"
#include "proof/proof_checker.h"
#include "smt/logic_exception.h"
#include "theory/arith/arith_evaluator.h"
#include "theory/arith/arith_rewriter.h"
#include "theory/arith/equality_solver.h"
#include "theory/arith/linear/simplex.h"
#include "theory/arith/linear/theory_arith_private.h"
#include "theory/arith/nl/nonlinear_extension.h"
#include "theory/arith/operator_elim.h"
#include "theory/ext_theory.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"
#include "util/cocoa_globals.h"
#include "util/finite_field_value.h"
#include "expr/skolem_manager.h"
#include "theory/smt_engine_subsolver.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {

TheoryArith::TheoryArith(Env& env, OutputChannel& out, Valuation valuation)
    : Theory(THEORY_ARITH, env, out, valuation),
      d_ppRewriteTimer(
          statisticsRegistry().registerTimer("theory::arith::ppRewriteTimer")),
      d_astate(env, valuation),
      d_im(env, *this, d_astate),
      d_ppre(d_env),
      d_bab(env, d_astate, d_im, d_ppre),
      d_eqSolver(nullptr),
      d_internal(env, d_astate, d_im, d_bab),
      d_nonlinearExtension(nullptr),
      d_opElim(d_env),
      d_arithPreproc(env, d_im, d_opElim),
      d_rewriter(nodeManager(), d_opElim, options().arith.arithExp),
      d_arithModelCacheSet(false),
      d_checker(nodeManager())
{
#ifdef CVC5_USE_COCOA
  // must be initialized before using CoCoA.
  initCocoaGlobalManager();
#endif /* CVC5_USE_COCOA */
  // indicate we are using the theory state object and inference manager
  d_theoryState = &d_astate;
  d_inferManager = &d_im;

  // construct the equality solver
  d_eqSolver.reset(new EqualitySolver(env, d_astate, d_im));
}

TheoryArith::~TheoryArith() {}

TheoryRewriter* TheoryArith::getTheoryRewriter() { return &d_rewriter; }

ProofRuleChecker* TheoryArith::getProofChecker() { return &d_checker; }

bool TheoryArith::needsEqualityEngine(EeSetupInfo& esi)
{
  // if the equality solver is enabled, then it is responsible for setting
  // up the equality engine
  return d_eqSolver->needsEqualityEngine(esi);
}
void TheoryArith::finishInit()
{
  const LogicInfo& logic = logicInfo();

  if (logic.isTheoryEnabled(THEORY_ARITH) && logic.areTranscendentalsUsed())
  {
    // witness is used to eliminate square root
    d_valuation.setUnevaluatedKind(Kind::WITNESS);
    // we only need to add the operators that are not syntax sugar
    d_valuation.setUnevaluatedKind(Kind::EXPONENTIAL);
    d_valuation.setUnevaluatedKind(Kind::SINE);
    d_valuation.setUnevaluatedKind(Kind::PI);
  }
  // only need to create nonlinear extension if non-linear logic
  if (logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear())
  {
    d_nonlinearExtension.reset(new nl::NonlinearExtension(d_env, *this));
  }
  d_eqSolver->finishInit();
  // finish initialize in the old linear solver
  eq::EqualityEngine* ee = getEqualityEngine();
  d_internal.finishInit(ee);

  // Set the congruence manager on the equality solver. If the congruence
  // manager exists, it is responsible for managing the notifications from
  // the equality engine, which the equality solver forwards to it.
  d_eqSolver->setCongruenceManager(d_internal.getCongruenceManager());
}

void TheoryArith::preRegisterTerm(TNode n)
{
  // handle logic exceptions
  Kind k = n.getKind();

  PolyInfo info = {false, {}};
  if (k == Kind::CONST_INTEGER || k == Kind::CONST_RATIONAL) {
    info.isPoly = true;
    info.vars = {};
  }
  else if (isTranscendentalKind(k)) info.isPoly = false;
  else if (n.isVar()) {
      std::string name = n.toString();
    if (name.find("@") == 0) {
        info.isPoly = false;
    }
    else {
        info.isPoly = true;
        info.vars.insert(n);
    }
  }
  else if (k == Kind::MULT || k == Kind::SUB || k == Kind::ADD || k == Kind::NONLINEAR_MULT) {
    bool allPoly = true;
    std::set<Node> allVars;
    for (size_t i = 0; i < n.getNumChildren(); i++) {
        auto it = d_polyExpMap.find(n[i]);
        if (it != d_polyExpMap.end() && it->second.isPoly) {
            allVars.insert(it->second.vars.begin(), it->second.vars.end());
        }
        else {
            allPoly = false;
            break;
        }
    }
    if(allPoly) {
        info = {true, allVars};
        Trace("crtsolver") << "poly: " << n << " yes, {";
        for (auto& var : allVars) {
            Trace("crtsolver") << var << ", ";
        }
        Trace("crtsolver") << "}" << std::endl;
    }
  }
  else if(k == Kind::EQUAL) {
      auto lhs = d_polyExpMap.find(n[0]);
      auto rhs = d_polyExpMap.find(n[1]);
      if (lhs != d_polyExpMap.end() && rhs != d_polyExpMap.end() && lhs->second.isPoly && rhs->second.isPoly) {
          std::set<Node> allVars;
          allVars.insert(lhs->second.vars.begin(), lhs->second.vars.end());
          allVars.insert(rhs->second.vars.begin(), rhs->second.vars.end());
          info = {true, allVars};
          Trace("crtsolver") << "poly equation found: " << n << " vars: {";
          for (auto& var : allVars) {
              Trace("crtsolver") << var << ", ";
          }
          Trace("crtsolver") << "}" << std::endl;
      }
  }
  d_polyExpMap[n] = info;
  if (info.isPoly && n.getKind() == Kind::EQUAL) {
      d_polyEquation[n] = info;
  }


  bool isTransKind = isTranscendentalKind(k);
  // note that we don't throw an exception for non-linear multiplication in
  // linear logics, since this is caught in the linear solver with a more
  // informative error message
  if (isTransKind || isExtendedNonLinearKind(k))
  {
    if (!options().arith.arithExp)
    {
      std::stringstream ss;
      ss << "Support for arithmetic extensions (required for " << k
         << ") not available in this configuration, try "
            "--arith-exp.";
      throw SafeLogicException(ss.str());
    }
    if (d_nonlinearExtension == nullptr)
    {
      std::stringstream ss;
      ss << "Term of kind " << k
         << " requires the logic to include non-linear arithmetic";
      throw LogicException(ss.str());
    }
    // logic exceptions based on the configuration of nl-ext: if we are a
    // transcendental function, we require nl-ext=full.
    if (isTransKind)
    {
      if (options().arith.nlExt != options::NlExtMode::FULL)
      {
        std::stringstream ss;
        ss << "Term of kind " << k
           << " requires nl-ext mode to be set to value 'full'";
        throw LogicException(ss.str());
      }
    }
    if (options().arith.nlCov && !options().arith.nlCovForce)
    {
      std::stringstream ss;
      ss << "Term of kind " << k
         << " is not compatible with using the coverings-based solver. If "
            "you know what you are doing, "
            "you can try --nl-cov-force, but expect crashes or incorrect "
            "results.";
      throw LogicException(ss.str());
    }
  }
  // if POW is allowed but was not rewritten
  if (k == Kind::POW || (k == Kind::POW2 && n[0].isConst()))
  {
    std::stringstream ss;
    ss << "The exponent of the POW(^) operator can only be a positive "
          "integral constant below "
       << (expr::NodeValue::MAX_CHILDREN + 1) << ". ";
    ss << "Exception occurred in:" << std::endl;
    ss << "  " << n;
    throw LogicException(ss.str());
  }
  if (d_nonlinearExtension != nullptr)
  {
    d_nonlinearExtension->preRegisterTerm(n);
  }
  else if (n.getKind() == Kind::NONLINEAR_MULT)
  {
    throw LogicException(
        "A non-linear term was asserted to arithmetic in a linear logic.");
  }
  d_internal.preRegisterTerm(n);
}

void TheoryArith::notifySharedTerm(TNode n)
{
  n = n.getKind() == Kind::TO_REAL ? n[0] : n;
  d_internal.notifySharedTerm(n);
}

TrustNode TheoryArith::ppRewrite(TNode atom, std::vector<SkolemLemma>& lems)
{
  CodeTimer timer(d_ppRewriteTimer, /* allow_reentrant = */ true);
  Trace("arith::preprocess") << "arith::ppRewrite() : " << atom << endl;
  Assert(d_env.theoryOf(atom) == THEORY_ARITH);
  // Eliminate operators. Notice we must do this here since other
  // theories may generate lemmas that involve non-standard operators. For
  // example, quantifier instantiation may use TO_INTEGER terms; SyGuS may
  // introduce non-standard arithmetic terms appearing in grammars.
  // call eliminate operators. In contrast to expandDefinitions, we eliminate
  // *all* extended arithmetic operators here, including total ones.
  return d_arithPreproc.eliminate(atom, lems, false);
}

TrustNode TheoryArith::ppStaticRewrite(TNode atom)
{
  Trace("arith::preprocess") << "arith::ppStaticRewrite() : " << atom << endl;
  Kind k = atom.getKind();
  if (k == Kind::EQUAL)
  {
    return d_ppre.ppRewriteEq(atom);
  }
  else if (k == Kind::GEQ)
  {
    // try to eliminate bv2nat from inequalities
    Node atomr = d_rewriter.rewriteIneqToBv(atom);
    if (atomr != atom)
    {
      return TrustNode::mkTrustRewrite(atom, atomr);
    }
  }
  return TrustNode::null();
}

bool TheoryArith::ppAssert(TrustNode tin,
                           TrustSubstitutionMap& outSubstitutions)
{
  return d_internal.ppAssert(tin, outSubstitutions);
}

void TheoryArith::ppStaticLearn(TNode n, std::vector<TrustNode>& learned)
{
  if (options().arith.arithStaticLearning)
  {
    d_internal.ppStaticLearn(n, learned);
  }
}

bool TheoryArith::preCheck(CVC5_UNUSED Effort level)
{
  Trace("arith-check") << "TheoryArith::preCheck " << level << std::endl;
  bool newFacts = !done();
  return d_internal.preCheck(newFacts);
}

void TheoryArith::postCheck(Effort level)
{
  d_im.reset();
  Trace("arith-check") << "TheoryArith::postCheck " << level << std::endl;
  if (Theory::fullEffort(level))
  {
    // Make sure we don't have old lemmas floating around. This can happen if we
    // didn't actually reach a last call effort check, but backtracked for some
    // other reason. In such a case, these lemmas are likely to be irrelevant
    // and possibly even harmful. If we produce proofs, their proofs have most
    // likely been deallocated already as well.
    d_im.clearPending();
    d_im.clearWaitingLemmas();
  }
  // we don't check at last call
  //Assert(level != Theory::EFFORT_LAST_CALL);
  // otherwise, check with the linear solver
  if (d_internal.postCheck(level))
  {
    // linear solver emitted a conflict or lemma, return
    return;
  }
  if (d_im.hasSent())
  {
    return;
  }

  if (Theory::fullEffort(level))
  {
    d_arithModelCache.clear();
    d_arithModelCacheIllTyped.clear();
    d_arithModelCacheSubs.clear();
    d_arithModelCacheSet = false;
    std::set<Node> termSet;
    if (d_nonlinearExtension != nullptr)
    {
      updateModelCache(termSet);
      // Check at full effort. This may either send lemmas or otherwise
      // buffer lemmas that we send at last call.
      d_nonlinearExtension->checkFullEffort(d_arithModelCache, termSet);
      // if we already sent a lemma, we are done
      if (d_im.hasSent())
      {
        return;
      }
    }
    else if (d_internal.foundNonlinear())
    {
      // set incomplete
      d_im.setModelUnsound(IncompleteId::ARITH_NL_DISABLED);
    }

    // If we won't be doing a last call effort check (which implies that
    // models will be computed), we must sanity check the integer model
    // from the linear solver now. We also must update the model cache
    // if we did not do so above.
    if (d_nonlinearExtension == nullptr)
    {
      updateModelCache(termSet);
    }
    sanityCheckIntegerModel();
    // Now, finalize the model cache, which constructs a substitution to be
    // used for getEqualityStatus.
    finalizeModelCache();

    // Plan B: full effort
    if (options().arith.arithCrtSolver == options::CrtSolverMode::FF) {
      //if (d_crtSolved) return;
      //d_crtCandidates.clear();
      NodeManager* nm = nodeManager();
      for (auto& eq : d_polyEquation) {
        Trace("candidate") << "eq: " << eq.first << std::endl;
        Node n = eq.first;
        d_crtCandidates.clear();
        for (int p : {2, 3, 5, 7, 11, 13, 17, 19, 23}) {
            TypeNode ffSort = nm->mkFiniteFieldType(Integer(p));
            std::map<Node, Node> nodeCache;
            Node ffEq = convertToFF(n, ffSort, nodeCache, d_crtFFMap[p]);
            if (ffEq.isNull()) {
                Trace("candidate") << "FF version is null skip " << ffEq << std::endl;
                continue;
            }
            Trace("crtsolver") << "FF version (modulus " << p << "): " << ffEq << std::endl;

            // collect ff variables for current prime
            std::vector<Node> ff_vars;
            for (auto& i : d_crtFFMap[p]) {
                ff_vars.push_back(i.second);
            }
            // model values to store values from subsolver
            std::vector<Node> model_vals;

            Options subopts;
            subopts.copyValues(d_env.getOptions());
            subopts.write_smt().produceModels = true;

            SubsolverSetupInfo ssi(d_env, subopts);
            Result result = checkWithSubsolver(ffEq, ff_vars, model_vals, ssi, true, 1000);
            Trace("candidate") << "subsolver result: " << result << std::endl;

            if (result.getStatus() == Result::SAT) {
                // extract candidate values from subsolver
                for (size_t i = 0; i < ff_vars.size(); i++) {
                    Integer val = model_vals[i].getConst<FiniteFieldValue>().toInteger();
                    // find which integer variable this ff var corresponds to
                    Node var;
                    for  (const auto& j : d_crtFFMap[p]) {
                        if (j.second == ff_vars[i]) {
                            var = j.first;
                            break;
                        }
                    }
                    if (var.isNull()){
                        continue; // skip to the next ff var
                    }

                    // crt combine with previous primes
                    auto it = d_crtCandidates.find(var);
                    if (it == d_crtCandidates.end()) {
                        // first prime for this variable so just store it
                        d_crtCandidates[var] = {Integer(p), val};

                    } else {
                        // crt combine with previous primes                        old mod          old remainder      new prime   new value
                        std::pair<Integer, Integer> combined = find_new_candidate(it->second.first, it->second.second, Integer(p), val);
                        d_crtCandidates[var] = combined;
                    }
                    Trace("candidate") << "candidate for " << var << ": " << d_crtCandidates[var].second << " mod " << d_crtCandidates[var].first << std::endl;
                }
            }
            if (result.getStatus() == Result::UNSAT) {
                TraceChannel("candidate") << "subsolver UNSAT mod " << p << std::endl;
                /* Node nn = nm->mkNode(Kind::IMPLIES ,n, ffEq);
                d_im.lemma(nn, InferenceId::ARITH_CRT_FF);
                return;
                */
                break;
            }
            if (populate_candidate_terms(n)) {
                d_crtSolved = true;
                return;
            }
        }
      }
    }
  }

  if (level == Theory::EFFORT_LAST_CALL)
  {
      Trace("candidate") << " effort last call works " << std::endl;
    // TODO: Add crt code PLAN C
    if (options().arith.arithCrtSolver == options::CrtSolverMode::FF) {
      //if (d_crtSolved) return;
      //d_crtCandidates.clear();
      TheoryModel* m = getValuation().getModel();
      NodeManager* nm = nodeManager();
      for (auto& eq : d_polyEquation) {
        Trace("candidate") << "eq: " << eq.first << std::endl;
        Node n = eq.first;
        d_crtCandidates.clear();
        for (int p : {2, 3, 5, 7, 11, 13, 17, 19, 23}) {
            for(auto& i : d_crtFFMap[p]) {
                Node var = i.first;
                Node ffVar = i.second;
                if (m->hasTerm(ffVar)) {
                    Node ffVal = m->getValue(ffVar);
                    Integer val = ffVal.getConst<FiniteFieldValue>().toInteger();
                    auto it = d_crtCandidates.find(var);
                    if (it == d_crtCandidates.end()) {
                        d_crtCandidates[var] = {Integer(p), val};
                    }
                    else {
                        std::pair<Integer, Integer> combined = find_new_candidate(it->second.first, it->second.second, Integer(p), val);
                        d_crtCandidates[var] = combined;
                    }
                }
            }
        }
        if (populate_candidate_terms(n)) {
            return;
        }
      }
    }
  }

}

bool TheoryArith::preNotifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  Trace("arith-check") << "TheoryArith::preNotifyFact: " << fact
                       << ", isPrereg=" << isPrereg
                       << ", isInternal=" << isInternal << std::endl;
  // We do not assert to the equality engine of arithmetic in the standard way,
  // hence we return "true" to indicate we are finished with this fact.
  bool ret = true;
  if (options().arith.arithEqSolver)
  {
    // the equality solver may indicate ret = false, after which the assertion
    // will be asserted to the equality engine in the default way.
    ret = d_eqSolver->preNotifyFact(atom, pol, fact, isPrereg, isInternal);
  }
  // we also always also notify the internal solver
  d_internal.preNotifyFact(fact);
  return ret;
}

bool TheoryArith::needsCheckLastEffort()
{
  if (d_nonlinearExtension != nullptr)
  {
    // If we computed lemmas in the last FULL_EFFORT check, send them now.
    if (d_im.hasPendingLemma())
    {
      Trace("arith-nl-buffer") << "Send buffered lemmas..." << std::endl;
      d_im.doPendingFacts();
      d_im.doPendingLemmas();
      d_im.doPendingPhaseRequirements();
    }
  }
  return true;
}

TrustNode TheoryArith::explain(TNode n)
{
  // if the equality solver has an explanation for it, use it
  TrustNode texp = d_eqSolver->explain(n);
  if (!texp.isNull())
  {
    return texp;
  }
  return d_internal.explain(n);
}

void TheoryArith::propagate(CVC5_UNUSED Effort e) { d_internal.propagate(); }

bool TheoryArith::collectModelInfo(TheoryModel* m,
                                   const std::set<Node>& termSet)
{
  // If we have a buffered lemma (from the non-linear extension), then we
  // do not assert model values, since those values are likely incorrect.
  // Moreover, the model does not need to satisfy the assertions, so
  // arbitrary values can be used for arithmetic terms. Hence, we just return
  // false here. The buffered lemmas will be sent immediately when asking if
  // a LAST_CALL effort should be performed (see needsCheckLastEffort).
  if (d_im.hasPendingLemma())
  {
    return false;
  }
  // this overrides behavior to not assert equality engine
  return collectModelValues(m, termSet);
}

bool TheoryArith::collectModelValues(TheoryModel* m,
                                     const std::set<Node>& termSet)
{
  if (TraceIsOn("arith::model"))
  {
    Trace("arith::model") << "arithmetic model after pruning" << std::endl;
    for (const auto& p : d_arithModelCache)
    {
      Trace("arith::model")
          << "\t" << p.first << " -> " << p.second << std::endl;
    }
  }

  updateModelCacheInternal(termSet);

  // We are now ready to assert the model.
  for (const std::pair<const Node, Node>& p : d_arithModelCache)
  {
    if (termSet.find(p.first) == termSet.end())
    {
      continue;
    }
    // do not assert non-leafs e.g. non-linear multiplication terms,
    // transcendental functions, etc.
    if (!Theory::isLeafOf(p.first, TheoryId::THEORY_ARITH))
    {
      continue;
    }
    // maps to constant of same type
    AssertEqual(p.first.getType(), p.second.getType())
        << "Bad type : " << p.first << " -> " << p.second;
    if (m->assertEquality(p.first, p.second, true))
    {
      continue;
    }
    else if (d_valuation.needCheck())
    {
      // If a theory solver has already sent a lemma in this context, we
      // know that theory engine will be called to recheck, so we can safely
      // return unsuccessfully here. Note that the arithmetic solver itself
      // may be the one that sent the lemma, for instance if we had buffered
      // lemmas during the call to needsCheckLastEffort.
      return false;
    }
    DebugUnhandled() << "A model equality could not be asserted: " << p.first
                     << " == " << p.second << std::endl;
    // If we failed to assert an equality, it is likely due to theory
    // combination, namely the repaired model for non-linear changed
    // an equality status that was agreed upon by both (linear) arithmetic
    // and another theory. In this case, we must add a lemma, or otherwise
    // we would terminate with an invalid model. Thus, we add a splitting
    // lemma of the form ( x = v V x != v ) where v is the model value
    // assigned by the non-linear solver to x.
    if (d_nonlinearExtension != nullptr)
    {
      Node eq = p.first.eqNode(p.second);
      Node lem = nodeManager()->mkNode(Kind::OR, eq, eq.negate());
      bool added = d_im.lemma(lem, InferenceId::ARITH_SPLIT_FOR_NL_MODEL);
      AlwaysAssert(added) << "The lemma was already in cache. Probably there "
                             "is something wrong with theory combination...";
    }
    return false;
  }
  return true;
}

void TheoryArith::notifyRestart() { d_internal.notifyRestart(); }

void TheoryArith::presolve() {
    d_internal.presolve();
    //Trace("candidate") << "presolve polyequation size: " << d_polyEquation.size() << std::endl;
    if(options().arith.arithCrtSolver == options::CrtSolverMode::FF && d_polyEquation.size() > 0)
    {
        NodeManager* nm = nodeManager();
        for (auto& eq : d_polyEquation)
        {
            Node n = eq.first;
            for (int p : {2, 3 , 5 , 7, 11 , 13}) {
                TypeNode ffSort = nm->mkFiniteFieldType(Integer(p));
                std::map<Node, Node> nodeCache;
                Node ffEq = convertToFF(n, ffSort, nodeCache, d_crtFFMap[p]);
                if (!ffEq.isNull()) {
                    Node lemma = nm->mkNode(Kind::IMPLIES, n, ffEq);
                    d_im.lemma(lemma, InferenceId::ARITH_CRT_FF);
                    Trace("candidate") << "presolve ffEq: " << ffEq << std::endl;
                }
            }
        }
    }
}

EqualityStatus TheoryArith::getEqualityStatus(TNode a, TNode b)
{
  Trace("arith-eq-status") << "TheoryArith::getEqualityStatus(" << a << ", "
                           << b << ")" << std::endl;
  if (a == b)
  {
    Trace("arith-eq-status") << "...return (trivial) true" << std::endl;
    return EQUALITY_TRUE_IN_MODEL;
  }
  if (d_arithModelCache.empty())
  {
    EqualityStatus es = d_internal.getEqualityStatus(a, b);
    Trace("arith-eq-status") << "...return (from linear) " << es << std::endl;
    return es;
  }
  Trace("arith-eq-status") << "Evaluate under " << d_arithModelCacheSubs.d_vars
                           << " / " << d_arithModelCacheSubs.d_subs
                           << std::endl;
  Node diff = nodeManager()->mkNode(Kind::SUB, a, b);
  // do not traverse non-linear multiplication here, since the value of
  // multiplication in this method should consider the value of the
  // non-linear multiplication term, and not its evaluation.
  std::optional<bool> isZero =
      isExpressionZero(d_env, diff, d_arithModelCacheSubs, false);
  if (isZero)
  {
    EqualityStatus es =
        *isZero ? EQUALITY_TRUE_IN_MODEL : EQUALITY_FALSE_IN_MODEL;
    Trace("arith-eq-status") << "...return (from evaluate) " << es << std::endl;
    return es;
  }
  Trace("arith-eq-status") << "...return unknown" << std::endl;
  return EQUALITY_UNKNOWN;
}

Node TheoryArith::getCandidateModelValue(TNode var)
{
  var = var.getKind() == Kind::TO_REAL ? var[0] : var;
  std::map<Node, Node>::iterator it = d_arithModelCache.find(var);
  if (it != d_arithModelCache.end())
  {
    return it->second;
  }
  return d_internal.getCandidateModelValue(var);
}

std::pair<bool, Node> TheoryArith::entailmentCheck(TNode lit)
{
  return d_internal.entailmentCheck(lit);
}

Node TheoryArith::convertToFF(TNode n, const TypeNode& ffSort, std::map<Node, Node>& nodeCache, std::map<Node, Node>& varMapping) {
    // check to avoid expononential number of nodes
    auto it = nodeCache.find(n);
    if (it != nodeCache.end()) return it->second;

    NodeManager* nm = nodeManager();
    Kind k = n.getKind();
    Node result;

    if (k == Kind::CONST_INTEGER){
        // integer constant to FF element (value mod p)
        Integer val = n.getConst<Rational>().getNumerator();
        Integer p = ffSort.getFfSize();
        result = nm->mkConst(FiniteFieldValue(val.floorDivideRemainder(p), FfSize(p)));
    }
    else if (n.isVar()){
        // variable to FF variable
        auto v = varMapping.find(n);
        if (v != varMapping.end()) result = v->second;
        else {
        SkolemManager* sm = nm->getSkolemManager();
        result = sm->mkDummySkolem("ff", ffSort);
        varMapping[n] = result;
        }
    }
    else if (k == Kind::MULT || k == Kind::NONLINEAR_MULT) {
        result = nm->mkNode(Kind::FINITE_FIELD_MULT, convertToFF(n[0], ffSort, nodeCache, varMapping), convertToFF(n[1], ffSort, nodeCache, varMapping));
    }
    else if (k == Kind::ADD) {
        result = nm->mkNode(Kind::FINITE_FIELD_ADD, convertToFF(n[0], ffSort, nodeCache, varMapping), convertToFF(n[1], ffSort, nodeCache, varMapping));
    }
    else if (k == Kind::SUB) {
        // x - y to x + neg(y)
        result = nm->mkNode(Kind::FINITE_FIELD_ADD, convertToFF(n[0], ffSort, nodeCache, varMapping), nm->mkNode(Kind::FINITE_FIELD_NEG, convertToFF(n[1], ffSort, nodeCache, varMapping)));
    }
    else if (k == Kind::EQUAL) {
        result = nm->mkNode(Kind::EQUAL, convertToFF(n[0], ffSort, nodeCache, varMapping), convertToFF(n[1], ffSort, nodeCache, varMapping));
    }
    else {
        result = Node::null(); // kind not supported
    }
    nodeCache[n] = result;
    return result;
}

//Node TheoryArith::convertToBV(Node n, const TypeNode& ffSort, std::map<Node, Node>& nodeCache, std::map<Node, Node>& varMapping) {}

std::pair<Integer,Integer> TheoryArith::calculate_coefficients(const Integer& m1, const Integer& m2) {
    if (m2 == 0) {
        // when m2 = 0, gcd(m1,m2) = m1
        // a1 = 1, a2 = 0
        return {1,0};
    }
    else {
        // gcd(m1, m2) = gcd(m2, m1 mod m2)

        Integer a = m1, b = m2;

        Integer x0 = 1, x1 = 0;
        Integer y0 = 0, y1 = 1;

        while (b != 0) {
            Integer q = a.floorDivideQuotient(b);
            Integer r = a.floorDivideRemainder(b);

            a = b;
            b = r;

            // Update x coefficients
            Integer tmpx = x1;
            x1 = x0 - q * x1;
            x0 = tmpx;

            // Update y coefficients
            Integer tmpy = y1;
            y1 = y0 - q * y1;
            y0 = tmpy;
        }
        // x0 is the coefficient for m1, y0 is the coefficient for m2
        return {x0, y0};
    }
}

// findnewcandidate uses chinese raminder theorem
/* x = r1 (mod m1), x = r2 (mod m2)
 * Bezout's identity: a1*m1 + a2*m2 = 1
 * Extended Euclidean algorithm: computes a1 and a2
 * x = (r1*a2*m2 + r2*a1*m1) mod m1*m2 */
std::pair<Integer,Integer> TheoryArith::find_new_candidate( const Integer& m1, const Integer& r1, const Integer& m2, const Integer& r2) {
    // Calculate coefficients for m1 and m2
    std::pair<Integer,Integer> coeffs = calculate_coefficients(m1, m2);
    Integer a1 = coeffs.first;
    Integer a2 = coeffs.second;

    Integer new_mod = m1 * m2; // Calculate the new modulus
    Integer new_result = (r1 * a2 * m2 + r2 * a1 * m1).floorDivideRemainder(new_mod);

    // ensure result is positive
    if (new_result < 0) {
        new_result += new_mod;
    }

    return {new_mod, new_result};
}

bool TheoryArith::populate_candidate_terms(Node n) {
    NodeManager* nm = nodeManager();
    for (const auto& i : d_crtCandidates) {
        Node var = i.first;
        Integer remainder = i.second.second;
        Integer mod = i.second.first;
        std::vector<Integer> offset_list = {Integer(0), mod , mod * Integer(-1), mod * Integer(2), mod * Integer(-2)};
        for (const Integer& offset : offset_list) {
            Integer new_val = remainder + offset;
            Node new_node = nm->mkConstInt(Rational(new_val));
            Node assign = nm->mkNode(Kind::EQUAL, var, new_node); // (= var (new_val))
            Node query = nm->mkNode(Kind::AND, n, assign); // (and (n) (new_node)

            SubsolverSetupInfo ssi(d_env);
            Result result = checkWithSubsolver(query,ssi,true ,1000);
            if (result.getStatus() == Result::SAT) {
                Trace("candidate") << "solution found: " << var << " = " << new_val << std::endl;
                return true;
            }
        }
    }
    return false;
}

eq::ProofEqEngine* TheoryArith::getProofEqEngine()
{
  return d_im.getProofEqEngine();
}

void TheoryArith::updateModelCache(std::set<Node>& termSet)
{
  if (!d_arithModelCacheSet)
  {
    collectAssertedTermsForModel(termSet);
    updateModelCacheInternal(termSet);
  }
}
void TheoryArith::updateModelCacheInternal(const std::set<Node>& termSet)
{
  if (!d_arithModelCacheSet)
  {
    d_arithModelCacheSet = true;
    d_internal.collectModelValues(
        termSet, d_arithModelCache, d_arithModelCacheIllTyped);
  }
}

void TheoryArith::finalizeModelCache()
{
  // make into substitution
  for (const auto& [node, repl] : d_arithModelCache)
  {
    Assert(repl.getType().isRealOrInt());
    // we only keep the domain of the substitution that is for leafs of
    // arithmetic; otherwise we are using the value of the abstraction of
    // non-linear term from the linear solver, which can be incorrect.
    if (Theory::isLeafOf(node, TheoryId::THEORY_ARITH))
    {
      d_arithModelCacheSubs.add(node, repl);
    }
  }
}

bool TheoryArith::sanityCheckIntegerModel()
{
  // Double check that the model from the linear solver respects integer types,
  // if it does not, add a branch and bound lemma. This typically should never
  // be necessary, but is needed in rare cases.
  if (Configuration::isAssertionBuild())
  {
    for (CVC5_UNUSED const auto& p : d_arithModelCache)
    {
      AssertEqual(p.first.getType(), p.second.getType())
          << "Bad type: " << p.first << " -> " << p.second;
    }
  }
  bool addedLemma = false;
  bool badAssignment = false;
  Trace("arith-check") << "model:" << std::endl;
  for (const auto& p : d_arithModelCacheIllTyped)
  {
    Trace("arith-check") << p.first << " -> " << p.second << std::endl;
    Assert(p.first.getType().isInteger() && !p.second.getType().isInteger());
    warning() << "TheoryArithPrivate generated a bad model value for "
                 "integer variable "
              << p.first << " : " << p.second << std::endl;
    // must branch and bound
    std::vector<TrustNode> lems =
        d_bab.branchIntegerVariable(p.first, p.second.getConst<Rational>());
    for (const TrustNode& lem : lems)
    {
      if (d_im.trustedLemma(lem, InferenceId::ARITH_BB_LEMMA))
      {
        addedLemma = true;
      }
    }
    badAssignment = true;
  }
  if (addedLemma)
  {
    // we had to add a branch and bound lemma since the linear solver assigned
    // a non-integer value to an integer variable.
    return true;
  }
  // this would imply that linear arithmetic's model failed to satisfy a branch
  // and bound lemma
  AlwaysAssert(!badAssignment)
      << "Bad assignment from TheoryArithPrivate::collectModelValues, and no "
         "branching lemma was sent";
  return false;
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
