#include "../include/SSAWriter.h"

#include <iostream>

namespace ssa_transform {

    bool SSAWriterVisitor::VisitFunctionDecl(clang::FunctionDecl *Declaration) {

        if(Declaration->isMain()) {
            CFG* cfg;

            Stmt* stmt = Declaration->getBody();

            // remove this later on... using it as unique pointer is better
            cfg = CFG::buildCFG(Declaration, stmt, Context, CFG::BuildOptions()).release();

            std::vector<bool> visited;
            for(unsigned int i = 0; i < cfg->size(); i++) {
                visited.push_back(false);
            }

            /*
            for(const auto &pair : phiPlacementMap) {
                for(const auto &phiFunc : pair.second) {
                    llvm::errs() << phiFunc.first << ": ";
                    for(const auto &elem : phiFunc.second) {
                        llvm::errs() << elem << " ";
                    }
                    llvm::errs() << "\n";
                }
            }
            */

            visitSeqCFGStmt(&(cfg->getEntry()), visited);
            llvm::errs() << "\n\nSSA Graph:\n";
            ssaGraph.clean();
            ssaGraph.print();

            /*
            std::string jsonFileName = srcFile + ".json";

            std::ofstream outputFileStream(jsonFileName);
            if(outputFileStream.is_open()) {
                ssaGraph.printAsJSON(outputFileStream);
                outputFileStream.close();
                llvm::outs() << "Wrote SSA graph for " << srcFile << " into " << jsonFileName << "\n";
            }
             */
            if(genmode == "-ssa") {
                ssaGraph.printAsJSON(std::cout);
            } else if(genmode == "-smt") {
                llvm::errs() << "Generating SMT\n";
                llvm::outs() << ssaGraph.getSMT(variableMap);
                llvm::errs() << "SMT Generated\n";

            } else {
                llvm::errs() << "No mode as " << genmode << "\n";
            }
        }

        return true;
    }

    /**
     * This constructs a SubSSANode depending on the expression type and the number and types of children for the expr
     * @param e
     * @return a unique pointer to an SSASubNode
     */
    std::unique_ptr<SSASubNode> SSAWriterVisitor::getSubSSANode(clang::Expr *e) {
        std::unique_ptr<SSASubNode> subNode = llvm::make_unique<SSASubNode>();
        if(llvm::isa<DeclRefExpr>(e)) {
            auto ref = llvm::dyn_cast<DeclRefExpr>(e);
            SourceLocation srcLoc = ref->getBeginLoc();
            subNode->parent = varReplacementMap[srcLoc];
            subNode->type = "Var";
        } else if(llvm::isa<CallExpr>(e)) {
            auto callExpr = llvm::dyn_cast<CallExpr>(e);

            auto functnDeclExpr = callExpr->getCallee()->IgnoreCasts();
            if(llvm::isa<DeclRefExpr>(functnDeclExpr)) {
                auto ref = llvm::dyn_cast<DeclRefExpr>(functnDeclExpr);
                subNode->parent = ref->getDecl()->getName();
                if(subNode->parent == "unknown") {
                    subNode->type = "UNK";
                    subNode->parent = "UNK_VAL";
                } else {
                    subNode->type = "func_call";
                    auto args = callExpr->getArgs();
                    for (unsigned int i = 0; i < callExpr->getNumArgs(); i++) {
                        subNode->args.push_back(getSubSSANode(args[i]->IgnoreCasts()->IgnoreParens()));
                    }
                }
            }

        } else if(llvm::isa<IntegerLiteral>(e)) {
            auto Int = llvm::dyn_cast<IntegerLiteral>(e);
            subNode->parent = Int->getValue().toString(10, true);
            subNode->type = "Const";
        } else if(llvm::isa<FloatingLiteral>(e)) {
            auto Float = llvm::dyn_cast<FloatingLiteral>(e);
            subNode->parent = std::to_string(Float->getValueAsApproximateDouble());
            subNode->type = "Const";
        } else if(llvm::isa<BinaryOperator>(e)) {
            auto binOp = llvm::dyn_cast<BinaryOperator>(e);
            subNode->parent = binOp->getOpcodeStr();
            subNode->type = "OP";
            subNode->args.push_back(getSubSSANode(binOp->getLHS()->IgnoreCasts()->IgnoreParens()));
            subNode->args.push_back(getSubSSANode(binOp->getRHS()->IgnoreCasts()->IgnoreParens()));
        } else if(llvm::isa<UnaryOperator>(e)) {
            auto unop = llvm::dyn_cast<UnaryOperator>(e);
            subNode->parent = clang::UnaryOperator::getOpcodeStr(unop->getOpcode());
            subNode->type = "OP";
            subNode->args.push_back(getSubSSANode(unop->getSubExpr()->IgnoreCasts()->IgnoreParens()));

            if(subNode->args[0]->type == "Const" && (subNode->parent == "+" || subNode->parent == "-")) {
                subNode->type = "Const";
                subNode->parent = subNode->parent + subNode->args[0]->parent;
                subNode->args.pop_back();
            }
        }
        return subNode;
    }

    /**
     * This constructs a SSANode depending on the expression type and the number and types of children for the expr
     * @param e
     * @return a unique pointer to an SSANode
     */
    std::unique_ptr<SSANode> SSAWriterVisitor::getSSANode(clang::Stmt *s) {
        // s->dump();
        std::unique_ptr<SSANode> ssaNode = llvm::make_unique<SSANode>();

        if(llvm::isa<BinaryOperator>(s)) {
            auto op = llvm::dyn_cast<BinaryOperator>(s);

            if(op->getOpcodeStr() == "=") {
                // op->dump();
                ssaNode->cmdName = "assign";
                ssaNode->cmd = "=";
                ssaNode->leftChild = getSubSSANode(op->getLHS()->IgnoreCasts()->IgnoreParens());
                ssaNode->rightChild = getSubSSANode(op->getRHS()->IgnoreCasts()->IgnoreParens());
                // llvm::errs() << "PRINTING THIS NODE:\n";
                // ssaNode->print();
                // llvm::errs() << "\n\n\n";
            } else if(op->isComparisonOp()) {
                // op->dump();
                ssaNode->cmdName = "if";
                ssaNode->cmd = "";
                ssaNode->rightChild = getSubSSANode(op);
                // llvm::errs() << "PRINTING THIS NODE:\n";
                // ssaNode->print();
                // llvm::errs() << "\n\n\n";
            }
        } else if(llvm::isa<CallExpr>(s)) {
            // first check if the called function is a RHS or not
            auto parent = Context->getParents(*s);
            if(!parent.empty()) {
                if(auto parentStmt = parent[0].get<Stmt>()) {
                    // llvm::errs() << parentStmt->getStmtClassName() << "\n";

                    if (llvm::isa<BinaryOperator>(parentStmt)) {
                        return nullptr;
                    } else if(llvm::isa<ImplicitCastExpr>(parentStmt)) {
                        ssaNode->cmdName = "";
                        return ssaNode;
                    }
                } else if(auto parentStmt = parent[0].get<VarDecl>()) {
                    return nullptr;
                }
            }

            auto callExpr = llvm::dyn_cast<CallExpr>(s);
            auto functnDeclExpr = callExpr->getCallee()->IgnoreCasts();
            if(llvm::isa<DeclRefExpr>(functnDeclExpr)) {
                auto ref = llvm::dyn_cast<DeclRefExpr>(functnDeclExpr);
                ssaNode->cmd = ref->getDecl()->getName();
                if(ssaNode->cmd.find("assert") != std::string::npos) {
                    // is an assert function
                    ssaNode->cmdName = "Assert";
                } else if(ssaNode->cmd.find("assume") != std::string::npos) {
                    ssaNode->cmdName = "Assume";
                } else {
                    ssaNode->cmdName = "func_call";
                }
                auto args = callExpr->getArgs();
                for(unsigned int i = 0; i < callExpr->getNumArgs(); i++) {
                    ssaNode->args.push_back(getSubSSANode(args[i]->IgnoreCasts()->IgnoreParens()));
                }

                // ssaNode->print();
                // llvm::errs() << "\n\n\n";
            }
        } else if(llvm::isa<UnaryOperator>(s)) {
            auto unop = llvm::dyn_cast<UnaryOperator>(s);
            ssaNode->cmdName = "if";
            ssaNode->cmd = "";
            ssaNode->rightChild = getSubSSANode(unop);
            // llvm::errs() << "PRINTING THIS NODE:\n";
            // ssaNode->print();
            // llvm::errs() << "\n\n\n";
        } else if(llvm::isa<DeclStmt>(s)) {
            auto declSt = llvm::dyn_cast<DeclStmt>(s);
            bool isinit = false;

            for (auto iter = declSt->decl_begin(); iter != declSt->decl_end(); iter++) {
                auto varDecl = llvm::dyn_cast<VarDecl>(*iter);

                if(varDecl->hasInit()) {
                    isinit = true;
                    ssaNode->cmdName = "assign";
                    ssaNode->cmd = "=";
                    ssaNode->leftChild = llvm::make_unique<SSASubNode>();
                    auto loc = varDecl->getLocation();
                    ssaNode->leftChild->parent = varReplacementMap[loc];
                    ssaNode->leftChild->type = "Var";
                    ssaNode->rightChild = getSubSSANode(varDecl->getInit()->IgnoreCasts()->IgnoreParens());
                }
            }

            if(!isinit) {
                return nullptr;
            }
        } else if(llvm::isa<ImplicitCastExpr>(s)) {
            auto castExpr = llvm::dyn_cast<ImplicitCastExpr>(s);
            // llvm::errs() << castExpr->getCastKindName() << "\n";
            if(std::string(castExpr->getCastKindName()).find("ToBoolean") != std::string::npos) {
                // find parent and see if it is either an if condition or it is a condition of a while or for loop
                auto parentList = Context->getParents(*s);
                if(!parentList.empty()) {
                    auto parent = parentList[0].get<Stmt>();
                    if(parent != nullptr) {
                        if(llvm::isa<IfStmt>(parent)) {
                            // llvm::errs() << "THIS IS IN AN IF STMT\n";
                            ssaNode->cmdName = "if";
                            ssaNode->cmd = "";
                            ssaNode->rightChild = getSubSSANode(castExpr->IgnoreImplicit()->IgnoreCasts()->IgnoreParens());
                            // llvm::errs() << "PRINTING THIS NODE:\n";
                            // ssaNode->print();
                            // llvm::errs() << "\n\n\n";
                        } else {

                            auto inLoop = isInLoop(castExpr);
                            if(inLoop.first == 0) {
                                // in for loop

                                auto forStmt = llvm::dyn_cast<ForStmt>(inLoop.second);
                                if(isWithin(s, forStmt->getCond())) {
                                    // llvm::errs() << "This is within a for condition\n";
                                    ssaNode->cmdName = "if";
                                    ssaNode->cmd = "";
                                    ssaNode->rightChild = getSubSSANode(castExpr->IgnoreImplicit()->IgnoreCasts()->IgnoreParens());
                                    // llvm::errs() << "PRINTING THIS NODE:\n";
                                    // ssaNode->print();
                                    // llvm::errs() << "\n\n\n";
                                }

                            } else if(inLoop.first == 1) {
                                // in while loop

                                auto whileStmt = llvm::dyn_cast<WhileStmt>(inLoop.second);
                                if(isWithin(s, whileStmt->getCond())) {
                                    // llvm::errs() << "This is within a while condition\n";
                                    ssaNode->cmdName = "if";
                                    ssaNode->cmd = "";
                                    ssaNode->rightChild = getSubSSANode(castExpr->IgnoreImplicit()->IgnoreCasts()->IgnoreParens());
                                    // llvm::errs() << "PRINTING THIS NODE:\n";
                                    // ssaNode->print();
                                    // llvm::errs() << "\n\n\n";
                                }

                            } else if(inLoop.first == 2) {
                                // in do..while loop

                                auto doWhileStmt = llvm::dyn_cast<DoStmt>(inLoop.second);
                                if(isWithin(s, doWhileStmt->getCond())) {
                                    // llvm::errs() << "This is within a do..while condition\n";
                                    ssaNode->cmdName = "if";
                                    ssaNode->cmd = "";
                                    ssaNode->rightChild = getSubSSANode(castExpr->IgnoreImplicit()->IgnoreCasts()->IgnoreParens());
                                    // llvm::errs() << "PRINTING THIS NODE:\n";
                                    // ssaNode->print();
                                    // llvm::errs() << "\n\n\n";
                                }

                            }
                        }
                    }
                }
            }
        }

        return ssaNode;
    }

    /**
     * This constructs an SSANode for a phi function
     * @param function
     * @return an SSANode unique pointer for a phi function
     */
    std::unique_ptr<SSANode> SSAWriterVisitor::getPhiNode(std::vector<std::string> &function) {
        auto phiNode = llvm::make_unique<SSANode>();
        phiNode->cmdName = "Phi";
        phiNode->cmd = "phi";

        phiNode->leftChild = llvm::make_unique<SSASubNode>();
        phiNode->leftChild->parent = function[0];
        phiNode->leftChild->type = "Var";

        phiNode->rightChild = llvm::make_unique<SSASubNode>();
        phiNode->rightChild->parent = "phi_merge";
        phiNode->rightChild->type = "OP";
        for(auto iter = function.begin() + 1; iter != function.end(); iter++) {
            if(!(*iter).empty()) {
                auto arg = llvm::make_unique<SSASubNode>();
                arg->parent = *iter;
                arg->type = "Var";
                phiNode->rightChild->args.push_back(std::move(arg));
            }
        }

        return phiNode;
    }

    /**
     * Checks if s is inside a for, while or do..while looop
     * @param s
     * @return a number indicating the type of loop and the loop statement
     */
    std::pair<int, clang::Stmt*> SSAWriterVisitor::isInLoop(clang::Stmt *s) {
        // if in no loop, return -1
        // if in for loop, return 0
        // if in while, return 1
        // if in do..while return 2

        auto parentStmts = Context->getParents(*s);
        if(!parentStmts.empty()) {
            auto parent = parentStmts[0].get<Stmt>();

            while(parent != nullptr) {
                if(llvm::isa<ForStmt>(parent)) {
                    return std::make_pair(0, const_cast<Stmt*>(parent));
                } else if(llvm::isa<WhileStmt>(parent)) {
                    return std::make_pair(1, const_cast<Stmt*>(parent));
                } else if(llvm::isa<DoStmt>(parent)) {
                    return std::make_pair(2, const_cast<Stmt*>(parent));
                } else {
                    parentStmts = Context->getParents(*parent);
                    if(!parentStmts.empty()) {
                        parent = parentStmts[0].get<Stmt>();
                    } else {
                        return std::make_pair(-1, const_cast<Stmt*>(parent));
                    }
                }
            }

            return std::make_pair(-1, const_cast<Stmt*>(parent));
        } else {
            return std::make_pair(-1, nullptr);
        }
    }

    /**
     * For a CFGBlock block, this function iterates over each CFGElement, gets them as statements and constructs the
     * appropriate SSANode for them and adds them to the SSAGraph along with the proper control flow.
     *
     * @todo Change this function to accept a Dominator Tree node, since we can get the CFGBlock from the Dominator Tree
     * and also that the Dominator tree does not have loops, which will make the visited vector unnecessary
     *
     * @param block
     * @param visited a boolean vector. visited[blockID] denotes if this block has been previously visited
     */
    void SSAWriterVisitor::visitSeqCFGStmt(clang::CFGBlock *block, std::vector<bool> &visited) {
        if(!visited.at(block->getBlockID())) {
            visited[block->getBlockID()] = true;
            if(block->pred_empty()) {
                // Entry node
                auto ssaNode = llvm::make_unique<SSANode>();
                ssaNode->cmdName = "SKIP";
                ssaNode->id = "ENTRY";
                for(auto succ : block->succs()) {
                    ssaGraph.addFlow(ssaNode->id, std::to_string(succ->getBlockID()) + "_1");
                }
                ssaGraph.addNode(ssaNode);
            } else if(block->succ_empty()) {
                // Exit node

                // check for phi functions
                int stmtNo = 1;

                auto phiFuncSet = phiPlacementMap[block->getBlockID()];
                int blkSize = phiFuncSet.size();

                for(auto phiFunc : phiFuncSet) {
                    auto phiNode = getPhiNode(phiFunc.second);
                    phiNode->id = std::to_string(block->getBlockID()) + "_" + std::to_string(stmtNo);
                    if(stmtNo == blkSize) {
                        ssaGraph.addFlow(phiNode->id, "EXIT");
                    } else {
                        ssaGraph.addFlow(phiNode->id,
                                         std::to_string(block->getBlockID()) + "_" + std::to_string(stmtNo + 1));
                    }
                    ssaGraph.addNode(phiNode);
                    stmtNo++;
                }

                auto ssaNode = llvm::make_unique<SSANode>();
                ssaNode->cmdName = "SKIP";
                ssaNode->id = "EXIT";

                ssaGraph.setExitNodeAltID(std::to_string(block->getBlockID()) + "_" + std::to_string(stmtNo));

                // The following loop gets all the control flows to the node ID and replaces the flow destination with
                // the EXIT id
                for(auto pair : ssaGraph.getControlFlow()) {
                    if(pair.second == std::to_string(block->getBlockID()) + "_" + std::to_string(stmtNo)) {
                        ssaGraph.addFlow(pair.first, ssaNode->id);
                        ssaGraph.eraseCtrlFlow(pair);
                    }
                }

                ssaGraph.addNode(ssaNode);
            } else {
                // llvm::errs() << "Statements in block " << block->getBlockID() << "\n";
                int stmtNo = 1;
                // stmtNo denotes the number of statements processed or under process

                if(!block->empty()) {

                    int newSizeOfBlock = block->size() + stmtNo - 1;

                    Stmt* firstStmt = nullptr;
                    if(!block->empty()) {
                        firstStmt = const_cast<Stmt*>((*block)[0].getAs<CFGStmt>()->getStmt());
                    }

                    // Iterate over all CFGElements of block, get them as Statements and then process each one
                    for (auto &I : *block) {
                        if (Optional<CFGStmt> CS = I.getAs<CFGStmt>()) {
                            const Stmt *s = CS->getStmt();
                            auto ssaNode = getSSANode(const_cast<Stmt *>(s));
                            if (ssaNode != nullptr) {

                                if(s == firstStmt) {

                                    if (block->pred_size() > 1) {
                                        // llvm::errs() << "IS THIS BLOCK " << block->getBlockID() << " IN ANY LOOP????\n";
                                        auto residentLoop = isInLoop(const_cast<Stmt *>(s));
                                        if (residentLoop.first == 0) {
                                            // in for loop
                                            auto forStmt = llvm::dyn_cast<ForStmt>(residentLoop.second);

                                            // some debugging stuff
                                            /*
                                            llvm::errs()
                                                    << s->getSourceRange().getBegin().printToString(Context->getSourceManager())
                                                    << " "
                                                    << s->getSourceRange().getEnd().printToString(Context->getSourceManager())
                                                    << "\n"
                                                    << forStmt->getCond()->getSourceRange().getBegin().printToString(Context->getSourceManager())
                                                    << " "
                                                    << forStmt->getCond()->getSourceRange().getEnd().printToString(Context->getSourceManager())
                                                    << "\n";

                                            llvm::errs() << isWithin(const_cast<Stmt*>(s), forStmt->getCond()) << "\n";
                                             */


                                            if (isWithin(const_cast<Stmt*>(s), forStmt->getCond())) {
                                                // add loop command before s node
                                                auto loopNode = llvm::make_unique<SSANode>();
                                                loopNode->cmdName = "Loop";
                                                loopNode->id = std::to_string(block->getBlockID()) + "_" + std::to_string(stmtNo);
                                                ssaGraph.addFlow(loopNode->id, std::to_string(block->getBlockID()) + "_" + std::to_string(stmtNo + 1));
                                                ssaGraph.addNode(loopNode);
                                                stmtNo++;
                                            }

                                        } else if (residentLoop.first == 1) {
                                            // in while loop

                                            auto whileStmt = llvm::dyn_cast<WhileStmt>(residentLoop.second);
                                            /*
                                            llvm::errs()
                                                    << s->getBeginLoc().printToString(Context->getSourceManager())
                                                    << " "
                                                    << whileStmt->getCond()->getBeginLoc().printToString(
                                                            Context->getSourceManager()) << "\n";
                                            */

                                            if(isWithin(const_cast<Stmt*>(s), whileStmt->getCond())) {
                                                auto loopNode = llvm::make_unique<SSANode>();
                                                loopNode->cmdName = "Loop";
                                                loopNode->id = std::to_string(block->getBlockID()) + "_" + std::to_string(stmtNo);
                                                ssaGraph.addFlow(loopNode->id, std::to_string(block->getBlockID()) + "_" + std::to_string(stmtNo + 1));
                                                ssaGraph.addNode(loopNode);
                                                stmtNo++;
                                            }

                                        } else if (residentLoop.first == 2) {
                                            // in do-while loop
                                            auto doStmt = llvm::dyn_cast<DoStmt>(residentLoop.second);
                                            // s->dump();
                                            // (*((*(doStmt->child_begin()))->child_begin()))->dump();
                                            /*
                                            llvm::errs() << s->getBeginLoc().printToString(Context->getSourceManager())
                                                         << " "
                                                         << (*((*(doStmt->child_begin()))->child_begin()))->getBeginLoc().printToString(
                                                                 Context->getSourceManager()) << "\n";
                                            */

                                            if(s->getBeginLoc() == (*((*(doStmt->child_begin()))->child_begin()))->getBeginLoc()) {
                                                auto loopNode = llvm::make_unique<SSANode>();
                                                loopNode->cmdName = "Loop";
                                                loopNode->id = std::to_string(block->getBlockID()) + "_" + std::to_string(stmtNo);
                                                ssaGraph.addFlow(loopNode->id, std::to_string(block->getBlockID()) + "_" + std::to_string(stmtNo + 1));
                                                ssaGraph.addNode(loopNode);
                                                stmtNo++;
                                            }
                                        }
                                    }

                                    // now to add phi functions if any

                                    auto phiFuncSet = phiPlacementMap[block->getBlockID()];
                                    for(auto phiFunc : phiFuncSet) {
                                        auto phiNode = getPhiNode(phiFunc.second);
                                        phiNode->id = std::to_string(block->getBlockID()) + "_" + std::to_string(stmtNo);
                                        ssaGraph.addFlow(phiNode->id, std::to_string(block->getBlockID()) + "_" + std::to_string(stmtNo + 1));
                                        ssaGraph.addNode(phiNode);
                                        stmtNo++;
                                    }

                                    newSizeOfBlock = block->size() + stmtNo - 1;
                                }

                                ssaNode->id = std::to_string(block->getBlockID()) + "_" + std::to_string(stmtNo);

                                if (stmtNo < newSizeOfBlock) {
                                    // this is not the last statement of the block
                                    ssaGraph.addFlow(ssaNode->id, std::to_string(block->getBlockID()) + "_" +
                                                                  std::to_string(stmtNo + 1));
                                } else if (stmtNo == newSizeOfBlock) {
                                    // this is the last statement in the block
                                    if(block->succ_size() == 1) {
                                        if(ssaGraph.isExitNode(std::to_string((*(block->succ_begin()))->getBlockID()) + "_1")) {
                                            ssaGraph.addFlow(ssaNode->id, "EXIT");
                                        } else {
                                            ssaGraph.addFlow(ssaNode->id,
                                                             std::to_string((*(block->succ_begin()))->getBlockID()) +
                                                             "_1");
                                        }
                                    } else if(block->succ_size() == 2) {
                                        // this shows that the block has an if condition and must split into two branches
                                        // a true and a false branch
                                        auto trueNode = llvm::make_unique<SSANode>();
                                        trueNode->cmdName = "TrueBranch";
                                        trueNode->cmd = "true";
                                        trueNode->id = std::to_string(block->getBlockID()) + "_" + std::to_string(stmtNo + 1);

                                        ssaGraph.addFlow(ssaNode->id, trueNode->id);


                                        auto falseNode = llvm::make_unique<SSANode>();
                                        falseNode->cmdName = "FalseBranch";
                                        falseNode->cmd = "false";
                                        falseNode->id = std::to_string(block->getBlockID()) + "_" + std::to_string(stmtNo + 2);
                                        ssaGraph.addFlow(ssaNode->id, falseNode->id);

                                        // first successor is in true branch
                                        if(ssaGraph.isExitNode(std::to_string((*(block->succ_begin()))->getBlockID()) + "_1")) {
                                            ssaGraph.addFlow(trueNode->id, "EXIT");
                                        } else {
                                            ssaGraph.addFlow(trueNode->id,
                                                             std::to_string((*(block->succ_begin()))->getBlockID()) +
                                                             "_1");
                                        }

                                        // second successor is in false branch
                                        if(ssaGraph.isExitNode(std::to_string((*(block->succ_begin() + 1))->getBlockID()) + "_1")) {
                                            ssaGraph.addFlow(falseNode->id, "EXIT");
                                        } else {
                                            ssaGraph.addFlow(falseNode->id, std::to_string(
                                                    (*(block->succ_begin() + 1))->getBlockID()) + "_1");
                                        }

                                        ssaGraph.addNode(trueNode);
                                        ssaGraph.addNode(falseNode);
                                    }
                                }
                                // llvm::errs() << "Added node " << ssaNode->id << " and cmdName " << ssaNode->cmdName << " to graph\n";
                                ssaGraph.addNode(ssaNode);

                                stmtNo++;
                            } else {
                                // ssaNode will be a nullpointer in events that do not concern the SSA, like declarations
                                // llvm::errs() << "No node of block " << block->getBlockID() << " and stmt " << stmtNo << " to graph\n";
                                if(stmtNo == newSizeOfBlock) {
                                    // if last statement
                                    // we now need to edit the destination nodes of all the predecessors to this CFGElement
                                    // we get the predecessors by checking which control flows point to the current stmtNo
                                    std::list<std::string> srcList;
                                    for(auto pair : ssaGraph.getControlFlow()) {
                                        if(pair.second == std::to_string(block->getBlockID()) + "_" + std::to_string(stmtNo)) {
                                            srcList.push_back(pair.first);
                                            ssaGraph.eraseCtrlFlow(pair);
                                        }
                                    }

                                    // Once we get the predecessors we now redirect their flows such that their control
                                    // goes to the first statement of the next block, or EXIT if the next case is the exit block

                                    for(auto succ : block->succs()) {
                                        for(auto src : srcList) {
                                            if (ssaGraph.isExitNode(std::to_string(succ->getBlockID()) + "_1")) {
                                                ssaGraph.addFlow(src, "EXIT");
                                            } else {
                                                ssaGraph.addFlow(src, std::to_string(succ->getBlockID()) + "_1");
                                            }
                                        }
                                    }

                                } else {
                                    newSizeOfBlock--;
                                }
                            }
                        }
                    }
                } else {
                    // Here the block is completely empty, signifying that this is probably a block where two branches
                    // merge, and so we must take care of any phi functions that may occur in this block

                    // llvm::errs() << "THE BLOCK IS EMPTY\n";

                    if(phiPlacementMap[block->getBlockID()].empty()) {
                        // no phi functions for this block
                        // We simply redirect the control flows of the block's predecessors to the block's successors

                        auto ctrlFlow = ssaGraph.getControlFlow();

                        for (const auto &pair : ctrlFlow) {
                            if (pair.second == std::to_string(block->getBlockID()) + "_1") {
                                for (auto succ : block->succs()) {
                                    ssaGraph.addFlow(pair.first, std::to_string(succ->getBlockID()) + "_1");
                                }

                                ssaGraph.eraseCtrlFlow(pair);
                            }
                        }
                    } else {
                        // here we just add phi functions similar to before
                        auto phiFuncSet = phiPlacementMap[block->getBlockID()];
                        unsigned long newSizeOfBlock = phiFuncSet.size();
                        for(auto phiFunc : phiFuncSet) {
                            auto phiNode = getPhiNode(phiFunc.second);
                            phiNode->id = std::to_string(block->getBlockID()) + "_" + std::to_string(stmtNo);
                            if(stmtNo != newSizeOfBlock) {
                                ssaGraph.addFlow(phiNode->id, std::to_string(block->getBlockID()) + "_" +
                                                              std::to_string(stmtNo + 1));
                            } else {
                                for(auto succ : block->succs()) {
                                    if(ssaGraph.isExitNode(std::to_string(succ->getBlockID()) + "_1")) {
                                        ssaGraph.addFlow(phiNode->id, "EXIT");
                                    } else {
                                        ssaGraph.addFlow(phiNode->id, std::to_string(succ->getBlockID()) + "_1");
                                    }
                                }
                            }
                            ssaGraph.addNode(phiNode);
                            stmtNo++;
                        }
                    }
                }
            }
            // llvm::errs() << "\n\n--------------------------------------------------------------\n\n";

            for(auto succ : block->succs()) {
                visitSeqCFGStmt(succ, visited);
            }

        }
    }
}