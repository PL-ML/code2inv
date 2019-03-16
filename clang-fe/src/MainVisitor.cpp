#include "../include/MainVisitor.h"

#include "../include/domfrontier.h"

namespace ssa_transform {
    using namespace clang;

    // the function that recursively visits each function decl
    bool MainFunctionVisitor::VisitFunctionDecl(clang::FunctionDecl *Declaration) {
        if(Declaration->isMain()) {
            DominatorTree dominatorTree;
            CFG* cfg;

            llvm::errs() << "\n\nAST for function " << Declaration->getName() << "\n";
            Declaration->dump();

            Stmt *body = Declaration->getBody();

            cfg = CFG::buildCFG(Declaration, body, Context, CFG::BuildOptions()).release();

            llvm::errs() << "\n\nCFG for function " << Declaration->getName() << "\n";
            cfg->dump(LangOptions(), true);

            AnalysisDeclContextManager contextManager(*Context, true);
            const Decl *decl = Declaration;
            AnalysisDeclContext analysisDeclContext(&contextManager, decl);
            // llvm::errs() << "CFG from analysis " << analysisDeclContext.getCFG() << "\n";

            // IMPORTANT
            // The buildDominatorTree method gives a SegFault for two of the 19 programs under the tests directory for
            // due to mysterious reasons
            // Needs to be fixed
            dominatorTree.buildDominatorTree(analysisDeclContext);

            dominatorTree.dump();

            // llvm::errs() << "Post order representation of dom tree: ";
            // printDomTree(dominatorTree.getRootNode());
            // llvm::errs() << "\n";

            DominanceFrontier dominanceFrontier;

            dominanceFrontier.calculateFrontiers(dominatorTree.getRootNode(), dominatorTree.DT);
            // dominanceFrontier.print();

            // used to get the CFGBlock of a statement given a map
            // returns a null pointer for DeclStmt with multiple VarDecls
            // to fix this the rewriter edits the code such that there is only one decl per declstmt
            cm = analysisDeclContext.getCFGStmtMap();

            // visitDeclStmt is used for getting the list of variables, their assignments and mapping the CFGBlocks to the
            // variable occurrences
            visitDeclStmt(Declaration->getBody());



            /*
            for(const auto &pair : assignments) {
                llvm::errs() << "Blocks of occurrence for " << pair.first << ":\t";
                for(auto blocks : pair.second) {
                    llvm::errs() << blocks->getBlockID() << " ";
                }
                llvm::errs() << "\n";
            }
             */


            phiPlacements = placePhi(assignments, dominanceFrontier.getFrontier(), *dominatorTree.DT);

            /*
            for(const auto &pair : phiPlacements) {
                llvm::errs() << "Phi functions in block " << pair.first->getBlockID() << " for: ";
                for(const auto &varNumArgPair : pair.second) {
                    llvm::errs() << "variable " << varNumArgPair.first << " with " << varNumArgPair.second.size() -1 << " args ";
                }
                llvm::errs() << "\n";
            }


            for(const auto &pair : blockVariableMap) {
                llvm::errs() << "Variables, statements and locs for block " << pair.first->getBlockID() << "\n";
                for(const auto &varStmtCollectn : pair.second) {
                    llvm::errs() << varStmtCollectn.var << "\n";
                    varStmtCollectn.stmt->dump();
                    llvm::errs() << varStmtCollectn.begin.printToString(Context->getSourceManager()) << " "
                                 << varStmtCollectn.end.printToString(Context->getSourceManager()) << "\n";
                    varStmtCollectn.islvalue ? llvm::errs() << "This is an lvalue\n\n" : llvm::errs() << "This is an rvalue\n\n";
                }
                llvm::errs() << "\n";
            }
            */

            renameVars(dominatorTree.DT);

            // llvm::errs() << "After renaming\n";

            // mapping the block ids to the phi functions instead of the CFGBlocks themselves
            // this is because if we map CFGBlock* to the functions, when the pass is complete, the CFGBlock* addresses
            // are no longer valid
            for(const auto &pair : phiPlacements) {
                blockPhiFuncMap[pair.first->getBlockID()] = pair.second;
            }
        }

        return true;
    }

    MainFunctionVisitor::varStmtStruct::varStmtStruct(std::string varName, clang::Stmt *varStmt,
                                                      clang::SourceLocation varBegin, clang::SourceLocation varEnd,
                                                      bool isLvalue, clang::ASTContext *ctx) {
        var = std::move(varName);
        stmt = varStmt;
        begin = varBegin;
        end = varEnd;
        islvalue = isLvalue;
        line = ctx->getSourceManager().getSpellingLineNumber(begin);
        col = ctx->getSourceManager().getSpellingColumnNumber(begin);
    }


    /**
     * We define a less than condition for the varStmtStruct so that when traversing a set of these structs, the variables
     * are considered from the top of the code to the bottom, but in each line they are viewed from left to right.
     * @param x
     * @return a bool
     */
    bool MainFunctionVisitor::varStmtStruct::operator<(
            const MainFunctionVisitor::varStmtStruct &x) const {
        if(line < x.line) {
            return true;
        } else if(line == x.line) {
            return col > x.col;
        } else {
            return false;
        }
    }

    bool MainFunctionVisitor::varStmtStruct::operator==(
            const MainFunctionVisitor::varStmtStruct &x) const {
        return var == x.var && stmt == x.stmt && begin == x.begin && end == x.end && islvalue == x.islvalue;
    }

    /**
     * printDeclStmt- Is not really supposed to print anything, but to get the list of variables into the variables vector,
     * information about said variable in blockVariableMap and the blocks where the variable gets assigned a value in
     * the assignments map.
     * @param stmt
     * @param cfg
     */
    void MainFunctionVisitor::visitDeclStmt(clang::Stmt *stmt) {
        if(std::string(stmt->getStmtClassName()) == "DeclStmt") {
            auto *declSt = llvm::dyn_cast<DeclStmt>(stmt);

            for (auto iter = declSt->decl_begin(); iter != declSt->decl_end(); iter++) {
                auto varDecl = llvm::dyn_cast<VarDecl>(*iter);
                std::string varName = varDecl->getDeclName().getAsString();
                variables[varName] = std::set<std::string>();
                // llvm::errs() << varName << "\n";

                // causes segfault when more than one vardecl in one stmt since for some reason cm->getBlock(stmt) gives 0x0
                blockVariableMap[cm->getBlock(stmt)].insert(
                        varStmtStruct(varName, stmt, varDecl->getLocation(), varDecl->getEndLoc(), true, Context));


                if(varDecl->hasInit()) {
                    // causes segfault when more than one vardecl in one stmt since for some reason cm->getBlock(stmt) gives 0x0
                    assignments[varName].insert(cm->getBlock(stmt));
                }
            }
        } else if(std::string(stmt->getStmtClassName()) == "BinaryOperator") {
            auto binOp = llvm::dyn_cast<BinaryOperator>(stmt);
            if(binOp->getOpcodeStr().str() == "=") {
                if(std::string(binOp->getLHS()->getStmtClassName()) == "DeclRefExpr") {
                    auto ref = llvm::dyn_cast<DeclRefExpr>(binOp->getLHS());
                    assignments[ref->getDecl()->getName()].insert(cm->getBlock(stmt));
                }
            }
        } else if(std::string(stmt->getStmtClassName()) == "DeclRefExpr") {
            auto ref = llvm::dyn_cast<DeclRefExpr>(stmt);
            if(std::string(ref->getDecl()->getDeclKindName()) == "Var") {

                // this now checks if the variable given by declrefexpr is an LValue or an RValue
                // this is done by checking the variable's parents
                // if it is an assignment operator (= sign), then var is an LValue
                // else RValue

                bool isLValue = false;
                auto parents = Context->getParents(*stmt);
                for(auto nodes : parents) {
                    auto st = nodes.get<Stmt>();
                    if(auto binst = llvm::dyn_cast<BinaryOperator>(st)) {
                        if((binst->getLHS() == ref)) {
                            isLValue = true;
                            Stmt* binSt = const_cast<Stmt*>(st);
                            blockVariableMap[cm->getBlock(stmt)].insert(
                                    varStmtStruct(ref->getDecl()->getName().str(), binSt, ref->getBeginLoc(), ref->getEndLoc(), true, Context));
                            break;
                        }
                    }
                }

                if(!isLValue) {
                    blockVariableMap[cm->getBlock(stmt)].insert(
                            varStmtStruct(ref->getDecl()->getName().str(), stmt, ref->getBeginLoc(), ref->getEndLoc(), false, Context));
                }
            }
        }
        for(auto st : stmt->children()) {
            if(st != nullptr) {
                visitDeclStmt(st);
            }
        }
    }

    void MainFunctionVisitor::printDomTree(clang::DomTreeNode *node) {
        auto children = node->getChildren();
        for(auto child : children) {
            printDomTree(child);
        }

        llvm::errs() << node->getBlock()->getBlockID() << " ";
    }

    int MainFunctionVisitor::whichPred(clang::CFGBlock *X, clang::CFGBlock *Y) {
        int i = 0;
        // we iterate reversed because in Cytron et al. the CFGBlocks are numbered in an ascending order while going from
        // entry to exit block, whereas the Clang's CFGBlocks are numbered in the descending order, resulting in a different
        // value for whichPred
        for(auto pred = Y->pred_rbegin(); pred != Y->pred_rend(); pred++) {
            if((*pred)->getBlockID() == X->getBlockID()) {
                return i;
            } else {
                i++;
            }
        }
        return -1;
    }

    void MainFunctionVisitor::search(clang::DomTreeNode *X, std::map<std::string, int> &C,
            std::map<std::string, std::stack<int>> &S) {
        CFGBlock* cfgX = X->getBlock();

        // first check for phi function
        // Cytron et al. considers phi functions to be at the beginning of the concerned block.
        for(auto& pair : phiPlacements[cfgX]) {
            // pair.first is the original variable for which the phi function is considered
            // pair.second is the vector consisting of the LHS of the phi function and the list of arguments
            // If the phi function is so: x_3 = phi(x_2, x_1, x_4), pair.second is a vector of elements x_3, x_2, x_1, x_4

            // args get taken care of later
            // we replace only pair.second[0] with the appropriate value now

            int i = C[pair.first];
            // pair.second.push_back(pair.first + "_" + std::to_string(i));
            pair.second[0] = pair.first + "_" + std::to_string(i);
            variables[pair.first].insert(pair.first + "_" + std::to_string(i));
            S[pair.first].push(i);
            C[pair.first] = i + 1;
        }

        for(const auto &varInfo : blockVariableMap[cfgX]) {
            // In Cytron et al. for each statement first the RHS variables are renamed and then the LHS variables get renamed
            // since our < condition for varStmtStruct dictates that in each statement, we traverse right to left,
            // simply iterating over the set lets us replace the variables as needed in the same order as Cytron et al. does

            if(varInfo.islvalue) {
                int i = C[varInfo.var];
                /*
                llvm::errs() << "Replace " << varInfo.var << " at "
                             << varInfo.begin.printToString(Context->getSourceManager())
                             << " by " << varInfo.var << "_" << i << "\n";
                */
                varReplacementMap[varInfo.begin] = varInfo.var + "_" + std::to_string(i);
                variables[varInfo.var].insert(varInfo.var + "_" + std::to_string(i));
                S[varInfo.var].push(i);
                C[varInfo.var] = i + 1;
            } else {
                int i = S[varInfo.var].top();
                /*
                llvm::errs() << "Replace " << varInfo.var << " at "
                             << varInfo.begin.printToString(Context->getSourceManager())
                             << " by " << varInfo.var << "_" << i << "\n";
                */
                varReplacementMap[varInfo.begin] = varInfo.var + "_" + std::to_string(i);
                variables[varInfo.var].insert(varInfo.var + "_" + std::to_string(i));
            }
        }

        for(auto iterY = cfgX->succ_rbegin(); iterY != cfgX->succ_rend(); iterY++) {

            // Here we again traverse in the reverse order for the same reason we traversed in reverse for whichPred

            auto Y = *iterY;
            // llvm::errs() << "Y is " << Y->getBlockID() << " and X is " << cfgX->getBlockID() << "\n";
            int j = whichPred(cfgX, Y);
            if(j != -1) {
                for(auto& phiFunc : phiPlacements[Y]) {
                    // llvm::errs() << "Before getting top... is stack for " << phiFunc.first << " empty? " << S[phiFunc.first].empty() << "\n";
                    // llvm::errs() << j << " is the position of the argument...\n";
                    int i;
                    if(S[phiFunc.first].empty()) {
                        // IMPORTANT- verify the accuracy of this method
                        // Sometimes the algorithm considers a block which has a phi function for a variable it has not
                        // encountered an assignment of yet. In such cases, the stack of said variable is empty and so
                        // S.top() is undefined, sometimes leading to segmentation faults. A possible fix is to consider
                        // this to be the 0th instance of the variable since it has not been declared/assigned yet
                        i = 0;
                    } else {
                        i = S[phiFunc.first].top();
                    }
                    // llvm::errs() << i << "\n";
                    if(std::find(phiFunc.second.begin(), phiFunc.second.end(), phiFunc.first + "_" + std::to_string(i))
                        == phiFunc.second.end()) {

                        phiFunc.second[j + 1] = phiFunc.first + "_" + std::to_string(i);
                        variables[phiFunc.first].insert(phiFunc.first + "_" + std::to_string(i));
                        // phiFunc.second.push_back(phiFunc.first + "_" + std::to_string(i));
                    }
                    /*
                    llvm::errs() << "Added variable " << phiFunc.first + "_" + std::to_string(i)
                                 << " to the phi function to " << phiFunc.second[0] << " in block "
                                 << Y->getBlockID() << " at position " << j << "\n";
                    */
                }
            }
        }

        for(auto Y : X->getChildren()) {
            // auto Y = *iterY;
            search(Y, C, S);
        }

        for(const auto &varInfo : blockVariableMap[cfgX]) {
            if(varInfo.islvalue) {
                S[varInfo.var].pop();
            }
        }

        for(const auto &pair: phiPlacements[cfgX]) {
            S[pair.first].pop();
        }
    }

    void MainFunctionVisitor::renameVars(llvm::DomTreeBase<clang::CFGBlock> *dominatorTree) {
        std::map<std::string, int> C;
        std::map<std::string, std::stack<int>> S;

        for(const auto &variablePair : variables) {
            C[variablePair.first] = 0;
        }

        search(dominatorTree->getRootNode(), C, S);
    }
}