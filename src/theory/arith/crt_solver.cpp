#include "theory/arith/crt_solver.h"
#include <cmath>
#include "theory/arith/theory_arith.h"
#include "theory/arith/inference_manager.h"
#include "theory/theory_model.h"
#include "options/smt_options.h"
#include "options/options.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

CrtSolver::CrtSolver(Env& env, TheoryState& st, InferenceManager& im) : EnvObj(env),d_st(st), d_im(im){}
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

void CrtSolver::planA() {
    if((options().arith.arithCrtSolver == options::CrtSolverMode::FF || options().arith.arithCrtSolver == options::CrtSolverMode::BV) && (options().arith.arithCrtArch == options::arithCrtArchMode::AC || options().arith.arithCrtArch == options::arithCrtArchMode::A) && d_polyEquation.size() > 0)
    {
        NodeManager* nm = nodeManager();
        bool isBV = (options().arith.arithCrtSolver == options::CrtSolverMode::BV);
        for (auto& eq : d_polyEquation)
        {
            Node n = eq.first;
            std::vector<int> crtPrimes = getCrtPrimes();
            for (int p : crtPrimes) {
                Node ffEq;
                std::map<Node, Node> nodeCache;
                unsigned bw = 0;
                if (isBV){
                    bw = (unsigned)std::ceil(std::log2((p-1) * (p-1 ) + 1 ));
                    TypeNode ffSort = nm->mkBitVectorType(bw);
                    ffEq = convertToBV(n, p, ffSort, nodeCache, d_crtBVMap[p]);
                }
                else{
                    TypeNode ffSort = nm->mkFiniteFieldType(Integer(p));
                    ffEq = convertToFF(n, ffSort, nodeCache, d_crtFFMap[p]);
                }
                if (!ffEq.isNull()) {
                    if (isBV) {
                        Node primeBV = nm->mkConst(BitVector(bw , (uint64_t)p));
                        std::vector<Node> eqns;
                        eqns.push_back(ffEq);
                        for (auto& i : d_crtBVMap[p]) {
                            eqns.push_back(nm->mkNode(Kind::BITVECTOR_ULT , i.second, primeBV));
                        }
                        ffEq = nm->mkNode(Kind::AND , eqns);
                    }

                    Node lemma = nm->mkNode(Kind::IMPLIES, n, ffEq);
                    d_im.lemma(lemma, InferenceId::ARITH_CRT_FF);
                    Trace("candidate") << "presolve ffEq: " << ffEq << std::endl;
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
    if ((options().arith.arithCrtSolver == options::CrtSolverMode::FF ||options().arith.arithCrtSolver == options::CrtSolverMode::BV) && options().arith.arithCrtArch == options::arithCrtArchMode::AC) {
        Trace("candidate") << "plan c used" << std::endl;
        TheoryModel* m = d_st.getValuation().getModel(); // used theoryarith object
        bool isBV = (options().arith.arithCrtSolver == options::CrtSolverMode::BV );
        d_crtCandidates.clear();
        std::vector<int> crtPrimes = getCrtPrimes();
        for (int p : crtPrimes) {
            auto& varMap = isBV? d_crtBVMap[p] : d_crtFFMap[p];

            for(auto& i : varMap) {
                Node var = i.first;
                Node ffVar = i.second;
                if (m->hasTerm(ffVar)) {
                    Node ffVal = m->getValue(ffVar);
                    Integer val = isBV? ffVal.getConst<BitVector>().getValue() : ffVal.getConst<FiniteFieldValue>().toInteger();

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

Node CrtSolver::convertToBV(TNode n, int prime, const TypeNode& bvSort, std::map<Node, Node>& nodeCache, std::map<Node, Node>& varMapping) {
    // check to avoid expononential number of nodes
    auto it = nodeCache.find(n);
    if (it != nodeCache.end()) return it->second;

    NodeManager* nm = nodeManager();
    Kind k = n.getKind();
    Node result;

    unsigned bw = bvSort.getBitVectorSize();
    Node primeBV = nm->mkConst(BitVector(bw, (uint64_t)prime));

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
    else if (k == Kind::MULT || k == Kind::NONLINEAR_MULT) {
        result = nm->mkNode(Kind::BITVECTOR_MULT, convertToBV(n[0], prime, bvSort, nodeCache, varMapping), convertToBV(n[1], prime, bvSort, nodeCache, varMapping));
        result = nm->mkNode(Kind::BITVECTOR_UREM, result, primeBV);
    }
    else if (k == Kind::ADD) {
        result = nm->mkNode(Kind::BITVECTOR_ADD, convertToBV(n[0], prime, bvSort, nodeCache, varMapping), convertToBV(n[1], prime, bvSort, nodeCache, varMapping));
        result = nm->mkNode(Kind::BITVECTOR_UREM, result, primeBV);
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

    std::vector<int> crtprimes = getCrtPrimes();
    for (int p : crtprimes) {
        Trace("candidate") << "CURRENT PRIME IN B MODE CRTSOLVER"<< p << std::endl;
        TypeNode ffSort;
        unsigned bw = 0;
        // sort depending on CRT mode
        if (isBV) {
            bw = (unsigned)std::ceil(std::log2((p - 1) * (p - 1) + 1));
            ffSort = nm->mkBitVectorType(bw);
        }
        else {
            ffSort = nm->mkFiniteFieldType(Integer(p));
        }

        for (auto& eq : d_polyEquation) {
            Node n = eq.first;
            std::map<Node, Node> nodeCache;
            // converting equation dpending on crt mode
            Node ffEq;
            if (isBV){
                ffEq = convertToBV(n, p, ffSort, nodeCache, d_crtBVMap[p]);
            }
            else{
                ffEq = convertToFF(n, ffSort, nodeCache, d_crtFFMap[p]);
            }
            if (ffEq.isNull()) {
                Trace("candidate") << "FF version is null skip " << ffEq << std::endl;
                continue;
            }
            Trace("crtsolver") << "FF version (modulus " << p << "): " << ffEq << std::endl;

            Trace("candidate") << "p=" << p << " eq=" << n << " null=" << ffEq.isNull() << std::endl;

            std::vector<Node> ff_vars;
            if (isBV) {
                // collect bv variables for current prime
                for (auto& i : d_crtBVMap[p]) {
                    ff_vars.push_back(i.second);
                }
            }
            else {
                // collect ff variables for current prime
                for (auto& i : d_crtFFMap[p]) {
                    ff_vars.push_back(i.second);
                }
            }

            // adding range assertions for BV
            if (isBV) {
                Node primeBV = nm->mkConst(BitVector(bw , (uint64_t)p));
                std::vector<Node> eqns;
                eqns.push_back(ffEq);
                for (auto& i : d_crtBVMap[p]) {
                    eqns.push_back(nm->mkNode(Kind::BITVECTOR_ULT , i.second, primeBV));
                }
                ffEq = nm->mkNode(Kind::AND , eqns);
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
                    Integer val;

                    if (isBV) {
                        val = model_vals[i].getConst<BitVector>().getValue();
                    }
                    else {
                        val = model_vals[i].getConst<FiniteFieldValue>().toInteger();
                    }
                    // find which integer variable this ff var corresponds to
                    Node var;
                    if (isBV) {
                        for  (const auto& j : d_crtBVMap[p]) {
                            if (j.second == ff_vars[i]) {
                                var = j.first;
                                break;
                            }
                        }
                    }
                    else {
                        for  (const auto& j : d_crtFFMap[p]) {
                            if (j.second == ff_vars[i]) {
                                var = j.first;
                                break;
                            }
                        }
                    }
                    if (var.isNull()){
                        continue; // skip to the next ff var
                    }

                    // crt combine with previous primes
                    auto& candidate = d_crtCandidates[n];
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
            if (result.getStatus() == Result::UNSAT) {
                Trace("candidate") << "subsolver UNSAT mod " << p << std::endl;
                Node nn = nm->mkNode(Kind::IMPLIES ,n, ffEq);
                d_im.lemma(nn, InferenceId::ARITH_CRT_FF);
                //d_im.conflict(n, InferenceId::ARITH_CRT_FF);
                return;
            }

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
