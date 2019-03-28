#include "../include/Rewriter.h"

namespace ssa_transform {
    using namespace clang;

    std::string RewriterClass::simplifyNot(clang::Expr *expr, int notLevel = 0) {
        // simplify a condition from !(a && b || c) and the like such that the && and || occur in the root of the condition
        // We use de Morgan's law which states that !(a && b) = !a || !b and !(a || b) = !a && !b

        if(llvm::isa<UnaryOperator>(expr)) {
            auto unOp = llvm::dyn_cast<UnaryOperator>(expr);
            if(clang::UnaryOperator::getOpcodeStr(unOp->getOpcode()) == "!") {
                auto subExpr = unOp->getSubExpr()->IgnoreParens()->IgnoreImplicit()->IgnoreCasts();

                const auto &sourceManager = rewriter.getSourceMgr();
                LangOptions lo;
                clang::SourceLocation b(subExpr->getBeginLoc()), _e(subExpr->getEndLoc());
                clang::SourceLocation e(clang::Lexer::getLocForEndOfToken(_e, 0, sourceManager, lo));

                std::string orgData = std::string(sourceManager.getCharacterData(b), sourceManager.getCharacterData(e) -
                                                                                     sourceManager.getCharacterData(b));


                return simplifyNot(subExpr, notLevel + 1);

            } else {
                const auto &sourceManager = rewriter.getSourceMgr();
                LangOptions lo;
                clang::SourceLocation b(expr->getBeginLoc()), _e(expr->getEndLoc());
                clang::SourceLocation e(clang::Lexer::getLocForEndOfToken(_e, 0, sourceManager, lo));

                std::string orgData = std::string(sourceManager.getCharacterData(b), sourceManager.getCharacterData(e) -
                                                                                     sourceManager.getCharacterData(b));

                // llvm::errs() << orgData << "\n";
                return orgData;
            }
        } else if(llvm::isa<BinaryOperator>(expr)) {
            auto binOp = llvm::dyn_cast<BinaryOperator>(expr);

            const auto &sourceManager = rewriter.getSourceMgr();
            LangOptions lo;
            clang::SourceLocation b(binOp->getBeginLoc()), _e(binOp->getEndLoc());
            clang::SourceLocation e(clang::Lexer::getLocForEndOfToken(_e, 0, sourceManager, lo));

            std::string orgData = std::string(sourceManager.getCharacterData(b), sourceManager.getCharacterData(e) -
                                                                                 sourceManager.getCharacterData(b));

            if(binOp->getOpcodeStr() == "&&") {

                std::string replacementOp;

                if(notLevel % 2) {
                    replacementOp = "||";
                } else {
                    replacementOp = "&&";
                }

                std::string res;

                res = "(";

                res.append(simplifyNot(binOp->getLHS()->IgnoreCasts()->IgnoreParens()->IgnoreImplicit(), notLevel));
                res.append(") ");
                res.append(replacementOp);
                res.append(" (");
                res.append(simplifyNot(binOp->getRHS()->IgnoreCasts()->IgnoreParens()->IgnoreImplicit(), notLevel));
                res.append(")");

                // llvm::errs() << orgData << " to " << res << "\n";

                return res;
            } else if (binOp->getOpcodeStr() == "||") {
                std::string replacementOp;

                if(notLevel % 2) {
                    replacementOp = "&&";
                } else {
                    replacementOp = "||";
                }

                std::string res;

                res = "(";

                res.append(simplifyNot(binOp->getLHS()->IgnoreCasts()->IgnoreParens()->IgnoreImplicit(), notLevel));
                res.append(") ");
                res.append(replacementOp);
                res.append(" (");
                res.append(simplifyNot(binOp->getRHS()->IgnoreCasts()->IgnoreParens()->IgnoreImplicit(), notLevel));
                res.append(")");

                llvm::errs() << orgData << " to " << res << "\n";

                return res;
            } else {
                // llvm::errs() << "Org Data is " << orgData << "\n";
                if(notLevel % 2) {
                    std::string res;

                    res = "!(";

                    res.append(simplifyNot(binOp->getLHS()->IgnoreCasts()->IgnoreParens()->IgnoreImplicit(), 0));
                    res.append(" ");
                    res.append(binOp->getOpcodeStr());
                    res.append(" ");
                    res.append(simplifyNot(binOp->getRHS()->IgnoreCasts()->IgnoreParens()->IgnoreImplicit(), 0));
                    res.append(")");
                    return res;
                } else {
                    std::string res;

                    res = "";

                    res.append(simplifyNot(binOp->getLHS()->IgnoreCasts()->IgnoreParens()->IgnoreImplicit(), 0));
                    res.append(" ");
                    res.append(binOp->getOpcodeStr());
                    res.append(" ");
                    res.append(simplifyNot(binOp->getRHS()->IgnoreCasts()->IgnoreParens()->IgnoreImplicit(), 0));

                    return res;
                    // return orgData;
                }

            }
        } else {
            const auto &sourceManager = rewriter.getSourceMgr();
            LangOptions lo;
            clang::SourceLocation b(expr->getBeginLoc()), _e(expr->getEndLoc());
            clang::SourceLocation e(clang::Lexer::getLocForEndOfToken(_e, 0, sourceManager, lo));

            if(b.isMacroID()) {
                auto expansionRange = sourceManager.getImmediateExpansionRange(b);
                b = expansionRange.getBegin();
            }
            std::string orgData = std::string(sourceManager.getCharacterData(b), sourceManager.getCharacterData(e) -
                                                                                 sourceManager.getCharacterData(b));

            // llvm::errs() << orgData << "\n";

            if(notLevel % 2) {
                return "!(" + orgData + ")";
            } else {
                return orgData;
            }
        }
    }

    bool RewriterClass::VisitStmt(clang::Stmt *s) {
        if(s != nullptr && context->getSourceManager().isInMainFile(s->getBeginLoc())) {
            if (isa<UnaryOperator>(s)) {
                // Either to simplify not statements or to rewrite ++ and -- operators as their simplified assignment
                // operators. eg- x++ -> x = x + 1

                auto unOp = llvm::dyn_cast<UnaryOperator>(s);
                const auto &sourceManager = rewriter.getSourceMgr();
                LangOptions lo;
                SourceRange range = unOp->getSourceRange();
                clang::SourceLocation b(unOp->getBeginLoc()), _e(unOp->getEndLoc());
                clang::SourceLocation e(clang::Lexer::getLocForEndOfToken(_e, 0, sourceManager, lo));

                std::string orgData = std::string(sourceManager.getCharacterData(b), sourceManager.getCharacterData(e) -
                                                                                     sourceManager.getCharacterData(b));

                CharSourceRange charSourceRange = Lexer::getAsCharRange(range, sourceManager, lo);
                charSourceRange.setEnd(e);

                if (isa<DeclRefExpr>(unOp->getSubExpr())) {
                    auto *ref = llvm::dyn_cast<DeclRefExpr>(unOp->getSubExpr());
                    std::string varName = ref->getDecl()->getName();
                    std::string op = clang::UnaryOperator::getOpcodeStr(unOp->getOpcode());
                    // llvm::errs() << ref->getDecl()->getName() << "\n";

                    if (op == "++") {
                        rewriter.RemoveText(charSourceRange);
                        rewriter.InsertText(b, varName + " = " + varName + " + 1");
                    } else if (op == "--") {
                        rewriter.RemoveText(charSourceRange);
                        rewriter.InsertText(b, varName + " = " + varName + " - 1");
                    }
                } else if(clang::UnaryOperator::getOpcodeStr(unOp->getOpcode()) == "!") {
                    clang::BeforeThanCompare<SourceLocation> isBefore(context->getSourceManager());
                    if(isBefore(lastNotChecked, b)) {
                        // ONLY USE SIMPLIFYNOT WHEN IT IS KNOWN THAT UNOP IS A NOT PREFIX
                        // NEVER OTHERWISE

                        // llvm::errs() << orgData << " becomes " << simplifyNot(unOp) << "\n";

                        // now to rewrite the stuff
                        std::string replacement = simplifyNot(unOp);
                        rewriter.RemoveText(charSourceRange);
                        rewriter.InsertText(b, replacement);
                        lastNotChecked = e;
                    }
                }

            } else if(isa<CompoundAssignOperator>(s)) {

                // Used to expand arithmetic shorthands like +=, -=, etc.

                auto compOp = llvm::dyn_cast<CompoundAssignOperator>(s);
                auto lhs = compOp->getLHS();
                auto rhs = compOp->getRHS()->IgnoreImpCasts();
                auto res = Expr::EvalResult();

                const auto &sourceManager = rewriter.getSourceMgr();
                LangOptions lo;
                SourceRange range = compOp->getSourceRange();
                clang::SourceLocation b(compOp->getBeginLoc()), _e(compOp->getEndLoc());
                clang::SourceLocation e(clang::Lexer::getLocForEndOfToken(_e, 0, sourceManager, lo));

                std::string orgData = std::string(sourceManager.getCharacterData(b), sourceManager.getCharacterData(e) -
                                                                                     sourceManager.getCharacterData(b));

                CharSourceRange charSourceRange = Lexer::getAsCharRange(range, sourceManager, lo);
                charSourceRange.setEnd(e);

                if(isa<DeclRefExpr>(lhs)) {
                    auto *lhsRef = llvm::dyn_cast<DeclRefExpr>(lhs);
                    std::string lhsVarName = lhsRef->getDecl()->getName();
                    std::string rhsVal;

                    if(rhs->EvaluateAsRValue(res, *context)) {
                        rhsVal = res.Val.getAsString(*context, rhs->getType());
                    } else if(isa<DeclRefExpr>(rhs)) {
                        auto* rhsRef = llvm::dyn_cast<DeclRefExpr>(rhs);
                        rhsVal = rhsRef->getDecl()->getName();
                    }

                    std::string op = compOp->getOpcodeStr();
                    std::string newExpr;
                    if(op == "+=") {
                        newExpr = lhsVarName + " = " + lhsVarName + " + " + rhsVal;
                    } else if(op == "-=") {
                        newExpr = lhsVarName + " = " + lhsVarName + " - " + rhsVal;
                    } else if(op == "*=") {
                        newExpr = lhsVarName + " = " + lhsVarName + " * " + rhsVal;
                    } else if(op == "/=") {
                        newExpr = lhsVarName + " = " + lhsVarName + " / " + rhsVal;
                    }

                    if(!newExpr.empty()) {
                        rewriter.RemoveText(charSourceRange);
                        rewriter.InsertText(b, newExpr);
                    }
                }
            } else if(isa<DeclStmt>(s)) {
                auto declStmt = llvm::dyn_cast<DeclStmt>(s);
                if(!declStmt->isSingleDecl()) {
                    // expand single statement with multiple declarations into multiple statements each with a single statement

                    const auto &sourceManager = rewriter.getSourceMgr();
                    LangOptions lo;
                    clang::SourceLocation b(declStmt->getBeginLoc()), _e(declStmt->getEndLoc());
                    clang::SourceLocation e(clang::Lexer::getLocForEndOfToken(_e, 0, sourceManager, lo));

                    std::string orgData = std::string(sourceManager.getCharacterData(b),
                                                      sourceManager.getCharacterData(e) -
                                                      sourceManager.getCharacterData(b));
                    // llvm::errs() << orgData << "\n";
                    SourceRange range = declStmt->getSourceRange();
                    CharSourceRange charSourceRange = Lexer::getAsCharRange(range, sourceManager, lo);
                    charSourceRange.setEnd(e);

                    std::string declString;

                    for (auto iter = declStmt->decl_begin(); iter != declStmt->decl_end(); iter++) {
                        if (isa<VarDecl>(*iter)) {
                            auto varDecl = llvm::dyn_cast<VarDecl>(*iter);
                            declString += varDecl->getType().getAsString() + " " + varDecl->getNameAsString();

                            if(varDecl->hasInit()) {
                                auto init = varDecl->getInit();
                                auto initRange = Lexer::getAsCharRange(init->getSourceRange(), sourceManager, lo);
                                auto initEnding = Lexer::getLocForEndOfToken(initRange.getEnd(), 0, sourceManager, lo);
                                auto initStr = std::string(sourceManager.getCharacterData(initRange.getBegin()),
                                                            sourceManager.getCharacterData(initEnding)
                                                            - sourceManager.getCharacterData(initRange.getBegin()));
                                declString += " = " + initStr;
                            }

                            declString += ";\n";
                        }
                    }

                    if(!declString.empty()) {
                        rewriter.RemoveText(charSourceRange);
                        rewriter.InsertText(b, declString);
                    }
                }
            } else if(isa<WhileStmt>(s)) {
                auto whileStmt = llvm::dyn_cast<WhileStmt>(s);
                auto whileCond = whileStmt->getCond()->IgnoreParens()->IgnoreCasts()->IgnoreImplicit();
                if(isa<IntegerLiteral>(whileCond)) {
                    // Integer Literal for now... we will add other stuff later
                    /**
                     * @todo Add support for floating literals
                     */

                    whileCond->dump();
                    const auto &sourceManager = rewriter.getSourceMgr();
                    LangOptions lo;
                    SourceRange range = whileCond->getSourceRange();
                    clang::SourceLocation b(whileCond->getBeginLoc()), _e(whileCond->getEndLoc());
                    clang::SourceLocation e(clang::Lexer::getLocForEndOfToken(_e, 0, sourceManager, lo));

                    CharSourceRange charSourceRange = Lexer::getAsCharRange(range, sourceManager, lo);
                    charSourceRange.setEnd(e);

                    auto intLiteral = llvm::dyn_cast<IntegerLiteral>(whileCond);

                    // llvm::errs() << intLiteral->getValue().toString(10, true) << "\n";

                    rewriter.InsertText(beginMain, "int cond" + std::to_string(numCond) + " = " + intLiteral->getValue().toString(10, true) + ";\n");
                    rewriter.RemoveText(charSourceRange);
                    rewriter.InsertText(b, "cond" + std::to_string(numCond));
                    numCond++;
                }
            } else if(isa<ForStmt>(s)) {
                auto forStmt = llvm::dyn_cast<ForStmt>(s);
                auto forCond = forStmt->getCond()->IgnoreParens()->IgnoreCasts()->IgnoreImplicit();
                if(isa<IntegerLiteral>(forCond)) {
                    // Integer Literal for now... we will add other stuff later

                    forCond->dump();
                    const auto &sourceManager = rewriter.getSourceMgr();
                    LangOptions lo;
                    SourceRange range = forCond->getSourceRange();
                    clang::SourceLocation b(forCond->getBeginLoc()), _e(forCond->getEndLoc());
                    clang::SourceLocation e(clang::Lexer::getLocForEndOfToken(_e, 0, sourceManager, lo));

                    CharSourceRange charSourceRange = Lexer::getAsCharRange(range, sourceManager, lo);
                    charSourceRange.setEnd(e);

                    auto intLiteral = llvm::dyn_cast<IntegerLiteral>(forCond);

                    // llvm::errs() << intLiteral->getValue().toString(10, true) << "\n";

                    rewriter.InsertText(beginMain, "int cond" + std::to_string(numCond) + " = " + intLiteral->getValue().toString(10, true) + ";\n");
                    rewriter.RemoveText(charSourceRange);
                    rewriter.InsertText(b, "cond" + std::to_string(numCond));
                    numCond++;
                }
            } else if(isa<DoStmt>(s)) {
                auto doStmt = llvm::dyn_cast<DoStmt>(s);
                auto doCond = doStmt->getCond()->IgnoreParens()->IgnoreCasts()->IgnoreImplicit();
                if(isa<IntegerLiteral>(doCond)) {
                    // Integer Literal for now... we will add other stuff later

                    doCond->dump();
                    const auto &sourceManager = rewriter.getSourceMgr();
                    LangOptions lo;
                    SourceRange range = doCond->getSourceRange();
                    clang::SourceLocation b(doCond->getBeginLoc()), _e(doCond->getEndLoc());
                    clang::SourceLocation e(clang::Lexer::getLocForEndOfToken(_e, 0, sourceManager, lo));

                    CharSourceRange charSourceRange = Lexer::getAsCharRange(range, sourceManager, lo);
                    charSourceRange.setEnd(e);

                    auto intLiteral = llvm::dyn_cast<IntegerLiteral>(doCond);

                    // llvm::errs() << intLiteral->getValue().toString(10, true) << "\n";

                    rewriter.InsertText(beginMain, "int cond" + std::to_string(numCond) + " = " + intLiteral->getValue().toString(10, true) + ";\n");
                    rewriter.RemoveText(charSourceRange);
                    rewriter.InsertText(b, "cond" + std::to_string(numCond));
                    numCond++;
                }
            }
        }

        return true;
    }

    void RewriterConsumer::HandleTranslationUnit(clang::ASTContext &Context) {
        Visitor.TraverseDecl(Context.getTranslationUnitDecl());
    }

    void RewriterClassAction::setRewrittenContentsAddress(std::string &newContent) {
        rewrittenContents = &newContent;
    }

    void RewriterClassAction::EndSourceFileAction() {
        llvm::raw_string_ostream newBuffer(*rewrittenContents);
        // llvm::errs() << rewriter.getRewriteBufferFor(compilerInstance->getSourceManager().getMainFileID()) << "\n";
        rewriter.getRewriteBufferFor(compilerInstance->getSourceManager().getMainFileID())->write(newBuffer);
        //llvm::errs() << "New content is\n" << newBuffer.str() << "\n\n";
    }

    std::unique_ptr<clang::ASTConsumer> RewriterClassAction::CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
        compilerInstance = &Compiler;
        LangOptions lo = Compiler.getLangOpts();
        SourceManager &sourceManager = Compiler.getSourceManager();
        rewriter.setSourceMgr(sourceManager, lo);

        rewriterConsumer = new RewriterConsumer(&Compiler.getASTContext(), rewriter);


        return std::unique_ptr<clang::ASTConsumer>(rewriterConsumer);
    }
}
