#include "../include/domfrontier.h"


/**
 * Calculates Dominance Frontiers based on algorithm in Fig. 10 of Cytron et al.
 * @param x The DomTreeNode whose frontiers we need
 * @param dominatorTree
 */

void ssa_transform::DominanceFrontier::calculateFrontiers(clang::DomTreeNode* x, llvm::DomTreeBase<clang::CFGBlock>* dominatorTree) {
    for(auto child : x->getChildren()) {
        calculateFrontiers(child, dominatorTree);
    }

    int idX = x->getBlock()->getBlockID();

    frontier[x].clear();

    // calculating dom frontier of current node
    // llvm::errs() << "Calculating for " << x->getBlock()->getBlockID() << "\n";
    for(auto y : x->getBlock()->succs()) {
        int idIdomY = dominatorTree->getNode(y)->getIDom()->getBlock()->getBlockID();

        if(idIdomY != idX) {
            frontier[x].insert(dominatorTree->getNode(y));
        }
    }

    for(auto z : x->getChildren()) {
        for(auto y : frontier[z]) {
            int idIdomY = y->getIDom()->getBlock()->getBlockID();
            if(idIdomY != idX) {
                frontier[x].insert(y);
            }
        }
    }
}


void ssa_transform::DominanceFrontier::print() {
    for(const auto &pair : frontier) {
        llvm::errs() << pair.first->getBlock()->getBlockID() << ": ";
        for(const auto &node : pair.second) {
            llvm::errs() << node->getBlock()->getBlockID() << " ";
        }

        llvm::errs() << "\n";
    }

    llvm::errs() << "\n";
}


ssa_transform::domFrontier ssa_transform::DominanceFrontier::getFrontier() {
    return frontier;
}

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

std::map <clang::CFGBlock*, std::list<std::pair<std::string, std::vector<std::string>>>> ssa_transform::placePhi(
        std::map<std::string, std::set<clang::CFGBlock *>> assignments, ssa_transform::domFrontier frontier,
        llvm::DomTreeBase<clang::CFGBlock>& dominatorTree) {

    // variable names as per Ron Cytron et al.

    std::map <clang::CFGBlock*, std::list<std::pair<std::string, std::vector<std::string>>>> phiPlacements;
    std::map<clang::CFGBlock*, int> hasAlready;
    std::map<clang::CFGBlock*, int> work;
    std::set<clang::CFGBlock*> W;

    int itercount = 0;

    for(const auto &pair : frontier) {
        hasAlready[pair.first->getBlock()] = 0;
        work[pair.first->getBlock()] = 0;
    }

    for(const auto& pair: assignments) {
        std::string variable = pair.first;

        itercount++;
        for(auto X : pair.second) {
            work[X] = itercount;
            W.insert(X);
        }

        while (!W.empty()) {
            clang::CFGBlock* X = (*W.begin());
            W.erase(X);
            for(auto Y : frontier[dominatorTree.getNode(X)]) {
                auto cfgBlockY = Y->getBlock();
                if(hasAlready[cfgBlockY] < itercount) {
                    phiPlacements[cfgBlockY].push_back(std::pair<std::string, std::vector<std::string>>(variable, std::vector<std::string>(cfgBlockY->pred_size() + 1)));
                    hasAlready[cfgBlockY] = itercount;
                    if(work[cfgBlockY] < itercount) {
                        work[cfgBlockY] = itercount;
                        W.insert(cfgBlockY);
                    }
                }
            }
        }
    }

    return phiPlacements;

}