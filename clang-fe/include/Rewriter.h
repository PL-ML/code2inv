#ifndef SSA_TRANSFORM_REWRITER_H
#define SSA_TRANSFORM_REWRITER_H

#include "clang/AST/Expr.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/AST/Expr.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Rewrite/Frontend/Rewriters.h"
#include "clang/Lex/Lexer.h"
#include "clang/Basic/Diagnostic.h"

namespace ssa_transform {

    /**
     * Rewriter Class- A class to rewrite the code to better suit the requirements for the SSA
     */
    class RewriterClass : public clang::RecursiveASTVisitor<RewriterClass> {
    private:
        clang::ASTContext *context;
        clang::Rewriter &rewriter;

        clang::SourceLocation lastNotChecked;
        int numCond;
        clang::SourceLocation beginMain;

        /**
         * simplifyNot- A function to simplify conditions surrounded by not, like !(c1 && c2) which interferes with the
         * SSAWriter's functioning
         *
         * @param expr
         * @param notLevel
         * @return a string to replace the original expression
         */
        std::string simplifyNot(clang::Expr* expr, int notLevel);

    public:
        /**
         * Actual rewriting is performed here
         *
         * @todo Restrict the statement visits to only those in main
         *
         * @param s
         * @return
         */
        bool VisitStmt(clang::Stmt *s);

        bool VisitFunctionDecl(clang::FunctionDecl* d) {

            lastNotChecked = d->getBeginLoc();

            if(d->isMain()) {
                numCond = 0;
                beginMain = (*d->getBody()->child_begin())->getBeginLoc();
                rewriter.InsertText(d->getBeginLoc(), "void assert(int cond);\nvoid assume(int cond);\nint unknown();\n");
                // (context->getDiagnostics()).dump();



                // d->dump();
            }

            return true;
        }

        RewriterClass(clang::ASTContext *astContext, clang::Rewriter &rewriter) : context(astContext), rewriter(rewriter) {}

    };

    class RewriterConsumer : public clang::ASTConsumer {
    public:
        explicit RewriterConsumer(clang::ASTContext* Context, clang::Rewriter& rewriter) : Visitor(Context, rewriter) {}

        virtual void HandleTranslationUnit(clang::ASTContext& Context);

    private:
        RewriterClass Visitor;
    };

    class RewriterClassAction : public clang::ASTFrontendAction {
    private:
        clang::Rewriter rewriter;
        clang::CompilerInstance* compilerInstance;
        RewriterConsumer* rewriterConsumer;
        std::string* rewrittenContents;
    public:

        void setRewrittenContentsAddress(std::string& newContent);

        void EndSourceFileAction() override;

        virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile) override;
    };
}


#endif //SSA_TRANSFORM_REWRITER_H
