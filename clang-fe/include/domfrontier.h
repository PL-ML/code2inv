/**
 * Contains a class to assist with the calculation of dominance frontiers, including local and up dominance as well as
 * a function to calculate the location of phi nodes as per Ron Cytron et al.
 */

#ifndef SSA_TRANSFORM_DOMFRONTIER_H
#define SSA_TRANSFORM_DOMFRONTIER_H

#include <map>
#include <vector>
#include <set>

#include "llvm/Analysis/LoopInfo.h"
#include "clang/Analysis/Analyses/Dominators.h"

namespace ssa_transform {

    typedef std::map<clang::DomTreeNode*, std::set<clang::DomTreeNode*>> domFrontier;

    class DominanceFrontier {
        domFrontier frontier;

    public:
        void calculateFrontiers(clang::DomTreeNode*, llvm::DomTreeBase<clang::CFGBlock>*);
        void print();
        domFrontier getFrontier();
    };

    /**
     * The phi placements are expressed as a map between a CFG block and a phi function
     * The phi function is a pair, with the first being the variable for said function
     * and the second being a vector of strings. The first element of the vector is the
     * LHS of the phi function, while the next n-1 elements are arguments 0, 1, ... n - 2
     * of the phi function.
     *
     * @param assignments- a map between a variable (given by a string) and the set of CFG blocks where it is assigned
     * @param frontier- the dominance frontier of different dominator tree nodes
     * @param dominatorTree- the dominator tree wrt which the domfrontier is found
     * @return a map between the CFGBlock and a phi function
     */
    std::map <clang::CFGBlock*, std::list<std::pair<std::string, std::vector<std::string>>>> placePhi(
            std::map<std::string, std::set<clang::CFGBlock*>> assignments, domFrontier frontier,
            llvm::DomTreeBase<clang::CFGBlock>& dominatorTree);

}

#endif //SSA_TRANSFORM_DOMFRONTIER_H
