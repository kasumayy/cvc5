#include "theory/arith/crt_solver.h"
#include <cmath>
#include "theory/arith/linear/simplex.h"
#include "theory/arith/operator_elim.h"
#include "theory/arith/theory_arith.h"
#include "theory/arith/inference_manager.h"
#include "theory/theory_model.h"
#include "options/smt_options.h"
#include "options/options.h"
#include "options/base_options.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

CrtSolver::CrtSolver(Env& env, TheoryState& st, InferenceManager& im) : EnvObj(env), d_assignment(context()), d_st(st), d_im(im), d_polyExpMap(userContext()), d_polyEquation(userContext()){
    //initializeSubsolver(d_subsolver, d_env);
}
CrtSolver::~CrtSolver(){};

void CrtSolver::PolyParser(TNode n) {
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
}

void CrtSolver::NotifyFact(TNode atom, bool pol) {
    d_assignment[atom] = pol;
    Trace("candidate") << "notifyfact " << atom << "is " << pol << std::endl;
}

void CrtSolver::planA() {
    //options().arith.arithCrtAuxConstraints && options().arith.arithCrtSolver != options::CrtSolverMode::OFF
    if(options().arith.arithCrtAuxConstraints && options().arith.arithCrtSolver != options::CrtSolverMode::OFF && d_polyEquation.size() > 0)
    {
        NodeManager* nm = nodeManager();
        bool isBV = (options().arith.arithCrtSolver == options::CrtSolverMode::BV);
        for (auto& eq : d_polyEquation)
        {
            Node n = eq.first;
            std::vector<int> crtPrimes = getCrtPrimes();
            for (int p : crtPrimes) {
                Node modEq;
                std::map<Node, Node> nodeCache;
                unsigned bw = 0;
                if (isBV){
                    bw = (unsigned)std::ceil(std::log2((p-1) * (p-1 ) + 1 ));
                    TypeNode ffSort = nm->mkBitVectorType(bw);
                    modEq = convertToBV(n, p, ffSort, nodeCache, d_crtBVMap[p]);
                }
                else{
                    TypeNode ffSort = nm->mkFiniteFieldType(Integer(p));
                    modEq = convertToFF(n, ffSort, nodeCache, d_crtFFMap[p]);
                }
                if (!modEq.isNull()) {
                    if (isBV) {
                        Node primeBV = nm->mkConst(BitVector(bw , (uint64_t)p));
                        std::vector<Node> eqns;
                        eqns.push_back(modEq);
                        for (auto& i : d_crtBVMap[p]) {
                            eqns.push_back(nm->mkNode(Kind::BITVECTOR_ULT , i.second, primeBV));
                        }
                        modEq = nm->mkNode(Kind::AND , eqns);
                    }

                    Node lemma = nm->mkNode(Kind::IMPLIES, n, modEq);
                    d_im.lemma(lemma, InferenceId::ARITH_CRT);
                    Trace("candidate") << "presolve ffEq: " << modEq << std::endl;
                }
            }
        }
    }
}


void CrtSolver::planB() {
    if ((options().arith.arithCrtSolver == options::CrtSolverMode::FF || options().arith.arithCrtSolver == options::CrtSolverMode::BV) && options().arith.arithCrtArch == options::arithCrtArchMode::B) {
      runCrtSolver();
    }
}

void CrtSolver::planC() {
    if ((options().arith.arithCrtSolver == options::CrtSolverMode::FF ||options().arith.arithCrtSolver == options::CrtSolverMode::BV) && options().arith.arithCrtArch == options::arithCrtArchMode::C && options().arith.arithCrtAuxConstraints) {
        Trace("candidate") << "plan c used" << std::endl;
        TheoryModel* m = d_st.getValuation().getModel(); // used theoryarith object
        bool isBV = (options().arith.arithCrtSolver == options::CrtSolverMode::BV );
        d_crtCandidates.clear();
        std::vector<int> crtPrimes = getCrtPrimes();
        for (int p : crtPrimes) {
            auto& varMap = isBV? d_crtBVMap[p] : d_crtFFMap[p];

            for(auto& i : varMap) {
                Node var = i.first;
                Node modVar = i.second;
                if (m->hasTerm(modVar)) {
                    Node modVal = m->getValue(modVar);
                    Integer val = isBV? modVal.getConst<BitVector>().getValue() : modVal.getConst<FiniteFieldValue>().toInteger();

                    for (auto& eq : d_polyEquation ) {
                        auto& candidate = d_crtCandidates[eq.first];
                        auto it = candidate.find(var);
                        if (it == candidate.end()) {
                            candidate[var] = {Integer(p), val};
                        }
                        else {
                            std::pair<Integer, Integer> combined = find_new_candidate(it->second.first, it->second.second, Integer(p), val);
                            candidate[var] = combined;
                        }
                    }

                }
            }
        }
        for (auto& eq : d_polyEquation) {
            if (populate_candidate_terms(eq.first)) {
                return;
            }
        }
    }
  }


Node CrtSolver::convertToFF(TNode n, const TypeNode& ffSort, std::map<Node, Node>& nodeCache, std::map<Node, Node>& varMapping) {
    // check to avoid expononential number of nodes
    auto it = nodeCache.find(n);
    if (it != nodeCache.end()) return it->second;

    NodeManager* nm = nodeManager();
    Kind k = n.getKind();
    Node result;

    auto convertChildren = [&](std::vector<Node>& childs) -> bool {
        for (size_t i = 0; i < n.getNumChildren(); i++) {
            Node c = convertToFF(n[i],ffSort, nodeCache, varMapping);
            if (c.isNull()) {
                return false;
            }
            childs.push_back(c);
        }
        return true;
    };

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
    else if (k == Kind::NEG) {
        Node v = convertToFF(n[0],ffSort, nodeCache, varMapping);
        if(!v.isNull()) {
            result = nm->mkNode(Kind::FINITE_FIELD_NEG, v);
        }
    }
    else if (k == Kind::MULT || k == Kind::NONLINEAR_MULT) {
        std::vector<Node> children;
        if (convertChildren(children)){
            result = nm->mkNode(Kind::FINITE_FIELD_MULT, children);
        }
    }
    else if (k == Kind::ADD) {
        std::vector<Node> children;
        if (convertChildren(children)){
            result = nm->mkNode(Kind::FINITE_FIELD_ADD, children);
        }
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

Node CrtSolver::convertToBV(TNode n, int prime, const TypeNode& bvSort, std::map<Node, Node>& nodeCache, std::map<Node, Node>& varMapping) {
    // check to avoid expononential number of nodes
    auto it = nodeCache.find(n);
    if (it != nodeCache.end()) return it->second;

    NodeManager* nm = nodeManager();
    Kind k = n.getKind();
    Node result;

    unsigned bw = bvSort.getBitVectorSize();
    Node primeBV = nm->mkConst(BitVector(bw, (uint64_t)prime));

    auto convertChildren = [&](std::vector<Node>& childs) -> bool {
        for (size_t i = 0; i < n.getNumChildren(); i++) {
            Node c = convertToBV(n[i], prime, bvSort, nodeCache, varMapping);
            if (c.isNull()) {
                return false;
            }
            childs.push_back(c);
        }
        return true;
    };

    if (k == Kind::CONST_INTEGER){
        Integer val = n.getConst<Rational>().getNumerator();
        Integer mod = val.floorDivideRemainder(Integer(prime));
        result = nm->mkConst(BitVector(bw, (uint64_t)mod.toUnsignedInt()) );
    }
    else if (n.isVar()){
        // variable to BV variable
        auto v = varMapping.find(n);
        if (v != varMapping.end()) result = v->second;
        else {
        SkolemManager* sm = nm->getSkolemManager();
        result = sm->mkDummySkolem("bv", bvSort);
        varMapping[n] = result;
        }
    }
    else if (k == Kind::NEG) {
        Node v = convertToBV(n[0], prime,bvSort, nodeCache, varMapping);
        if (!v.isNull()) {
            result = nm->mkNode(Kind::BITVECTOR_SUB, primeBV, v);
            result = nm->mkNode(Kind::BITVECTOR_UREM, result,primeBV);
        }
    }
    else if (k == Kind::MULT || k == Kind::NONLINEAR_MULT) {
        std::vector<Node> children;
        if(convertChildren(children)) {
            Node current = children[0];
            for (size_t i = 1; i < children.size(); i++) {
                current = nm->mkNode(Kind::BITVECTOR_MULT, current, children[i]);
                current = nm->mkNode(Kind::BITVECTOR_UREM, current, primeBV);
            }
            result = current;
        }
    }
    else if (k == Kind::ADD) {
        std::vector<Node> children;
        if(convertChildren(children)) {
            Node current = children[0];
            for (size_t i = 1; i < children.size(); i++) {
                current = nm->mkNode(Kind::BITVECTOR_ADD, current, children[i]);
                current = nm->mkNode(Kind::BITVECTOR_UREM, current, primeBV);
            }
            result = current;
        }
    }
    else if (k == Kind::SUB) {
        result = nm->mkNode(Kind::BITVECTOR_SUB, convertToBV(n[0], prime, bvSort, nodeCache, varMapping), convertToBV(n[1], prime, bvSort, nodeCache, varMapping));
        result = nm->mkNode(Kind::BITVECTOR_UREM, result, primeBV);
    }
    else if (k == Kind::EQUAL) {
        result = nm->mkNode(Kind::EQUAL, convertToBV(n[0], prime, bvSort, nodeCache, varMapping), convertToBV(n[1], prime, bvSort, nodeCache, varMapping));
    }
    else {
        result = Node::null(); // kind not supported
    }
    nodeCache[n] = result;
    return result;
}

void CrtSolver::runCrtSolver() {

    NodeManager* nm = nodeManager();
    d_crtCandidates.clear();
    bool isBV = (options().arith.arithCrtSolver == options::CrtSolverMode::BV);

    if(d_subsolver == nullptr) {
        Options subopts;
        subopts.copyValues(d_env.getOptions());
        subopts.write_smt().produceModels = true;
        subopts.write_smt().unsatAssumptions = true;
        subopts.write_base().incrementalSolving = true;
        SubsolverSetupInfo ssi(d_env, subopts);
        initializeSubsolver(nm,d_subsolver,ssi);
    }

    std::vector<int> crtprimes = getCrtPrimes();
    for (int p : crtprimes) {
        Trace("candidate") << "CURRENT PRIME IN B MODE CRTSOLVER"<< p << std::endl;
        TypeNode typeSort;
        unsigned bw = 0;
        // sort depending on CRT mode
        if (isBV) {
            bw = (unsigned)std::ceil(std::log2((p - 1) * (p - 1) + 1));
            typeSort = nm->mkBitVectorType(bw);
        }
        else {
            typeSort = nm->mkFiniteFieldType(Integer(p));
        }

        std::vector<Node> assumptions;
        std::map<Node,Node> booltoeqn;
        std::vector<Node> type_vars;

        for (auto& eq : d_polyEquation) {
            Node n = eq.first;
            auto curr = d_assignment.find(n);
            if (curr == d_assignment.end() || !(*curr).second){
                continue;
            }
            Node eqBool;
            auto boolIt = d_subeqns[p].find(n);
            if (boolIt != d_subeqns[p].end()){
                eqBool = boolIt->second;
            }
            else {
                std::map<Node, Node> nodeCache;
                // converting equation dpending on crt mode
                Node modEq;
                if (isBV){
                    modEq = convertToBV(n, p, typeSort, nodeCache, d_crtBVMap[p]);
                }
                else{
                    modEq = convertToFF(n, typeSort, nodeCache, d_crtFFMap[p]);
                }
                if (modEq.isNull()) {
                    Trace("candidate") << "FF version is null skip " << modEq << std::endl;
                    continue;
                }
                Trace("crtsolver") << "FF version (modulus " << p << "): " << modEq << std::endl;

                Trace("candidate") << "p=" << p << " eq=" << n << " null=" << modEq.isNull() << std::endl;

                // adding range assertions for BV
                if (isBV) {
                    Node primeBV = nm->mkConst(BitVector(bw , (uint64_t)p));
                    std::vector<Node> eqns;
                    eqns.push_back(modEq);
                    for (auto& i : d_crtBVMap[p]) {
                        eqns.push_back(nm->mkNode(Kind::BITVECTOR_ULT , i.second, primeBV));
                    }
                    modEq = nm->mkNode(Kind::AND , eqns);
                }
                // one boolean per euation per prime
                SkolemManager* sm = nm->getSkolemManager();
                eqBool = sm->mkDummySkolem("crteq", nm->booleanType());
                d_subsolver->assertFormula(nm->mkNode(Kind::IMPLIES, eqBool, modEq));
                d_subeqns[p][n] = eqBool;
            }
            assumptions.push_back(eqBool);
            booltoeqn[eqBool] = n;

            type_vars.clear();
            if (isBV) {
                // collect bv variables for current prime
                for (auto& i : d_crtBVMap[p]) {
                    type_vars.push_back(i.second);
                }
            }
            else {
                // collect ff variables for current prime
                for (auto& i : d_crtFFMap[p]) {
                    type_vars.push_back(i.second);
                }
            }
        }

            if (assumptions.empty()) {
                continue;
            }

            Result result = d_subsolver->checkSat(assumptions);
            Trace("candidate") << "subsolver result: " << result << std::endl;

            if (result.getStatus() == Result::SAT) {
                // extract candidate values from subsolver
                for (size_t i = 0; i < type_vars.size(); i++) {
                    Node model_vals = d_subsolver->getValue(type_vars[i]);
                    Integer val;

                    if (isBV) {
                        val = model_vals.getConst<BitVector>().getValue();
                    }
                    else {
                        val = model_vals.getConst<FiniteFieldValue>().toInteger();
                    }
                    // find which integer variable this ff var corresponds to
                    Node var;
                    if (isBV) {
                        for  (const auto& j : d_crtBVMap[p]) {
                            if (j.second == type_vars[i]) {
                                var = j.first;
                                break;
                            }
                        }
                    }
                    else {
                        for  (const auto& j : d_crtFFMap[p]) {
                            if (j.second == type_vars[i]) {
                                var = j.first;
                                break;
                            }
                        }
                    }
                    if (var.isNull()){
                        continue; // skip to the next ff var
                    }

                    // storing all equaitons for the same model to use
                    for (auto& z : assumptions) {
                        Node eqn = booltoeqn[z];
                        // crt combine with previous primes
                        auto& candidate = d_crtCandidates[eqn];
                        auto it = candidate.find(var);
                        if (it == candidate.end()) {
                            // first prime for this variable so just store it
                            candidate[var] = {Integer(p), val};
                        } else {
                            // crt combine with previous primes                        old mod          old remainder      new prime   new value
                            std::pair<Integer, Integer> combined = find_new_candidate(it->second.first, it->second.second, Integer(p), val);
                            candidate[var] = combined;
                        }
                        Trace("candidate") << "candidate for " << var << ": " << candidate[var].second << " mod " << candidate[var].first << std::endl;
                    }
                }
            }
            if (result.getStatus() == Result::UNSAT) {
                Trace("candidate") << "subsolver UNSAT mod " << p << std::endl;
                // finding whic bool equations cause unsat assumptions
                std::vector<Node> boolunsat = d_subsolver->getUnsatAssumptions();
                std::vector<Node> cause;
                for (Node i : boolunsat) {
                    auto eqIt = booltoeqn.find(i);
                    if (eqIt != booltoeqn.end()) {
                        cause.push_back(eqIt->second);
                    }
                }
                if (cause.empty()){
                    continue;
                }

                Node nn = cause.size() == 1 ? cause[0] : nm->mkNode(Kind::AND, cause);
                d_im.conflict(nn, InferenceId::ARITH_CRT);
                //d_im.conflict(n, InferenceId::ARITH_CRT);
                return;
            }
    }
    for (auto& eq : d_polyEquation) {
        if (populate_candidate_terms(eq.first)) {
            return;
        }
    }
}

std::vector<int> CrtSolver::getCrtPrimes() {
    int size = (int)options().arith.arithCrtPrimes;

    if (options().arith.arithCrtSolver == options::CrtSolverMode::FF) {
        std::vector<int> primes;
        int candidate = 2;
        while ((int)primes.size() < size) {
            bool isPrime = true;
            for (int p : primes) {
                if (candidate % p == 0) {
                    isPrime = false;
                    break;
                }
            }
            if (isPrime) {
                primes.push_back(candidate);
            }
            candidate++;
        }
        return primes;
    }
    else if (options().arith.arithCrtSolver == options::CrtSolverMode::BV) {
        // primes near power of 2
        std::vector<int> primes;
        // left bit shift is 2^n
        int n = 2;
        while ((int)primes.size() < size) {
            int min = (1 << n) -1;
            if (poly::is_prime(min)) primes.push_back(min);

            int max = (1 << n) + 1;
            if(poly::is_prime(max)) primes.push_back(max);

            n++;
        }
        return primes;
    }
    return {};
}

std::pair<Integer,Integer> CrtSolver::calculate_coefficients(const Integer& m1, const Integer& m2) {
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
std::pair<Integer,Integer> CrtSolver::find_new_candidate( const Integer& m1, const Integer& r1, const Integer& m2, const Integer& r2) {
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

bool CrtSolver::populate_candidate_terms(Node n) {
    NodeManager* nm = nodeManager();
    std::vector<Node> vars;
    std::vector<Integer> remainder;
    std::vector<Integer> mod;

    for (const auto& i : d_crtCandidates[n]) {
        vars.push_back(i.first);
        remainder.push_back(i.second.second);
        mod.push_back(i.second.first);
    }
    if (vars.empty()) {
        return false;
    }
    size_t varsize = vars.size();
    // std::vector<Integer> offset_list = {Integer(0), mod , mod * Integer(-1), mod * Integer(2), mod * Integer(-2)};
    std::vector<int> offset_multiplier = {0,1,-1,2,-2};
    std::vector<size_t> index(varsize,0);

    while (true) {
        Node tmp = n;
        for (size_t i = 0; i < varsize; i++) {
            Integer new_val = remainder[i] + mod[i] * Integer(offset_multiplier[index[i]]);
            Node new_node = nm->mkConstInt(Rational(new_val));
            //Node assign = nm->mkNode(Kind::EQUAL, var, new_node); // (= var (new_val))
            //Node query = nm->mkNode(Kind::AND, n, assign); // (and (n) (new_node)
            tmp = tmp.substitute(TNode(vars[i]), TNode(new_node));
        }
        Node check = rewrite(tmp);
        if (check == nm->mkConst(true)){
            //Trace("candidate") << "solution found: " << var << " = " << new_val << std::endl;
            Trace("candidate") << "solution found: " << n << std::endl;
            return true;
        }
        size_t curr = 0;
        while (curr < varsize) {
            index[curr]++;
            if (index[curr] < offset_multiplier.size())
            {
                break;
            }
            else
            {
                index[curr] = 0;
                curr++;
            }
        }
        if (curr == varsize)
        {
            break;
        }
    }
    return false;
}



}
}
}
