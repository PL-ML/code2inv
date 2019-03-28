#include <utility>

#include <utility>

#include <utility>

#include <utility>

#ifndef SSA_TRANSFORM_SSAWRITER_H
#define SSA_TRANSFORM_SSAWRITER_H

#include <fstream>
#include <utility>
#include <clang/Frontend/FrontendAction.h>
#include <clang/Frontend/CompilerInstance.h>

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/ADT/APFloat.h"

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Analysis/CFG.h"
#include "clang/Basic/LangOptions.h"
#include "clang/Basic/SourceLocation.h"
#include "clang/AST/Stmt.h"
#include "clang/Analysis/CFGStmtMap.h"
#include "clang/AST/Expr.h"
#include "clang/Lex/Lexer.h"

#include "SSAGraph.h"

namespace ssa_transform {

    using namespace clang;

    class SSAWriterVisitor : public RecursiveASTVisitor<SSAWriterVisitor> {
    public:
        explicit SSAWriterVisitor(
                ASTContext* Context, std::map<clang::SourceLocation, std::string> varRepmap,
                std::map<int, std::list<std::pair<std::string, std::vector<std::string>>>>& phiPlaceMap,
                std::map<std::string, std::set<std::string>> varMap, std::string filename, std::string mode) :
                Context(Context), varReplacementMap(std::move(varRepmap)), phiPlacementMap(phiPlaceMap),
                variableMap(std::move(varMap)), srcFile(std::move(filename)), genmode(std::move(mode)) {
            lo = Context->getLangOpts();
            sm = &Context->getSourceManager();
        }

        bool VisitFunctionDecl(FunctionDecl* Declaration);



    private:
        ASTContext* Context;
        std::map<clang::SourceLocation, std::string> varReplacementMap;
        std::map<std::string, std::set<std::string>> variableMap;
        std::map<int, std::list<std::pair<std::string, std::vector<std::string>>>> phiPlacementMap;
        clang::LangOptions lo;
        clang::SourceManager* sm;
        SSAGraph ssaGraph;
        std::string srcFile;
        std::string genmode;

        std::unique_ptr<SSASubNode> getSubSSANode(Expr* e);

        std::unique_ptr<SSANode> getSSANode(Stmt* s);

        std::unique_ptr<SSANode> getPhiNode(std::vector<std::string>& function);

        /**
         * Checks if a statement is in a loop. If so, return the parent loop statment (either ForStmt, WhileStmt or DoStmt)
         * and a number corresponding to the parent statement (-1 No loop, 0 ForStmt, 1 WhileStmt, 2 DoStmt)
         * @param s
         */
        std::pair<int, clang::Stmt*> isInLoop(Stmt* s);

        /// checks if statement s1 is within statement s2
        bool isWithin(Stmt* s1, Stmt* s2) {
            // Checks if stmt1 is within stmt2
            clang::BeforeThanCompare<SourceLocation> isBefore(Context->getSourceManager());
            return (isBefore(s2->getBeginLoc(), s1->getBeginLoc()) || s2->getBeginLoc() == s1->getBeginLoc()) &&
                   (isBefore(s1->getEndLoc(), s2->getEndLoc()) || s1->getEndLoc() == s2->getEndLoc());
        }

        /**
         * Visit CFGStmt sequentially as per the control flow and add SSANodes to the SSAGraph
         *
         * @todo Try and optimize the placement of the SSANodes to avoid the need of the SSAGraph::clean() function
         *
         * @param block
         * @param visited
         */

        void visitSeqCFGStmt(CFGBlock* block, std::vector<bool>& visited);
    };

    class SSAWriterConsumer : public clang::ASTConsumer {
    public:
        explicit SSAWriterConsumer(
                clang::ASTContext* Context, const std::map<clang::SourceLocation, std::string>& varRepMap,
                std::map<int, std::list<std::pair<std::string, std::vector<std::string>>>>& phiPlaceMap,
                std::map<std::string, std::set<std::string>> varMap, std::string filename, std::string mode) :

                Visitor(Context, varRepMap, phiPlaceMap, std::move(varMap), std::move(filename), std::move(mode)) {}

        virtual void HandleTranslationUnit(clang::ASTContext& Context) {
            Visitor.TraverseDecl(Context.getTranslationUnitDecl());
        }

    private:
        SSAWriterVisitor Visitor;
    };

    class SSAWriterFrontAction : public clang::ASTFrontendAction {
        std::string filename;
        std::map<clang::SourceLocation, std::string> varReplacementMap;
        std::map<int, std::list<std::pair<std::string, std::vector<std::string>>>> phiPlacementMap;
        std::map<std::string, std::set<std::string>> variableMap;
        std::string mode;
    public:
        explicit SSAWriterFrontAction(
                const std::map<clang::SourceLocation, std::string>& varRepMap,
                std::map<int, std::list<std::pair<std::string, std::vector<std::string>>>> & phiPlaceMap,
                std::map<std::string, std::set<std::string>> varMap, std::string fname, std::string mode) {
            varReplacementMap = varRepMap;
            phiPlacementMap = phiPlaceMap;
            filename = std::move(fname);
            variableMap = std::move(varMap);
            this->mode = std::move(mode);
        }

        virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
            llvm::errs() << "Mode is " << mode << "\n";
            return std::unique_ptr<clang::ASTConsumer>(
                    new SSAWriterConsumer(
                            &Compiler.getASTContext(), varReplacementMap, phiPlacementMap, variableMap, filename, mode));
        }
    };

}

#endif //SSA_TRANSFORM_SSAWRITER_H
