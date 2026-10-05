#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__CRT_SOLVER_H
#define CVC5__THEORY__ARITH__CRT_SOLVER_H

#include <vector>
#include <map>
#include <unordered_map>
#include <utility>
#include <set>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/smt_engine_subsolver.h"
#include "util/bitvector.h"
#include "util/finite_field_value.h"

namespace cvc5::internal {
namespace theory {
class TheoryState;
namespace arith {
class InferenceManager;

class CrtSolver : EnvObj {
    public:
        CrtSolver(Env& env, TheoryState& st, InferenceManager& im);
        ~CrtSolver();

        void PolyParser(TNode n);
        void planA();
        void planB();
        void planC();

    private:
        /** CRT: convert an integer term to its finite field equivalent */
        Node convertToFF(TNode n, const TypeNode& ffSort, std::map<Node, Node>& nodeCache, std::map<Node, Node>& varMapping);
        /** CRT: convert an integer term to its bitvector equivalent */
        Node convertToBV(TNode n, int prime, const TypeNode& bvSort, std::map<Node, Node>& nodeCache, std::map<Node, Node>& varMapping);
        /** CRT: run the CRT solver */
        void runCrtSolver();
        /** CRT: generate a list of prime numbers for the CRT solver */
        std::vector<int> getCrtPrimes();
        /** CRT: uses extended euclidean algorithm where it returns bezout coefficients */
        std::pair<Integer,Integer> calculate_coefficients(const Integer& m1, const Integer& m2);
        /** CRT: uses chinese remainder theorem where it returns the new modulus and remainder */
        std::pair<Integer,Integer> find_new_candidate( const Integer& m1, const Integer& r1, const Integer& m2, const Integer& r2);
        /** CRT: populates candidate terms for the CRT solver and tries the candaditates to see if it can solve the equation */
        bool populate_candidate_terms(Node n);

        /** CRT Polynomial decection */
        struct PolyInfo {
          bool isPoly;
          std::set<Node> vars;
          };
          std::unordered_map<Node, PolyInfo> d_polyExpMap;
          std::unordered_map<Node, PolyInfo> d_polyEquation;
        /** CRT finite field conversion */
        std::map<int, std::map<Node, Node>> d_crtFFMap;
        /** CRT Bit Vector conversion */
        std::map<int, std::map<Node, Node>> d_crtBVMap;
        /** CRT running candidates (modulus, remainder) */
        std::map < Node, std::map<Node, std::pair<Integer, Integer>>> d_crtCandidates;
        /** subsolver */
        std::unique_ptr<SolverEngine> d_subsolver;

        TheoryState& d_st;
        InferenceManager& d_im;
};
}
}
}

#endif
