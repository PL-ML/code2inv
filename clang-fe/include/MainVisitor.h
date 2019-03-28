#ifndef SSA_TRANSFORM_MAINVISITOR_H
#define SSA_TRANSFORM_MAINVISITOR_H


#include <fstream>
#include <string>
#include <iostream>
#include <vector>
#include <exception>
#include <unordered_set>

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/ADT/APFloat.h"

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Analysis/AnalysisDeclContext.h"
#include "clang/Analysis/CFG.h"
#include "clang/Basic/LangOptions.h"
#include "clang/Basic/SourceLocation.h"
#include "clang/Analysis/Analyses/Dominators.h"
#include "clang/AST/Stmt.h"
#include "clang/Analysis/CFGStmtMap.h"
#include "clang/AST/ParentMap.h"
#include "clang/AST/Expr.h"

namespace ssa_transform {

    class MainFunctionVisitor : public clang::RecursiveASTVisitor<MainFunctionVisitor> {
    public:
        explicit MainFunctionVisitor(clang::ASTContext *Context) : Context(Context) {}

        bool VisitFunctionDecl(clang::FunctionDecl *Declaration);

        std::map<clang::SourceLocation, std::string> getVarReplacementMap() {
            return varReplacementMap;
        }

        std::map<int, std::list<std::pair<std::string, std::vector<std::string>>>> getBlockPhiPlacementMap() {
            return blockPhiFuncMap;
        }

        std::map <std::string, std::set<std::string>> getVariableMap() {
            return variables;
        }

    private:
        clang::ASTContext *Context;

        /**
         * varStmtStruct- This is a structure which contains the information about a variable. Each occurrence of a
         * variable in the parsed program will have an instantiation of the structure associated with it. The structure
         * has info about the original variable name, the statement it occurs in and the location of the variable.
         */
        struct varStmtStruct {
            int line, col;
            std::string var;
            clang::Stmt *stmt;
            clang::SourceLocation begin;
            clang::SourceLocation end;
            bool islvalue;

            varStmtStruct(
                    std::string varName, clang::Stmt *varStmt, clang::SourceLocation varBegin,
                    clang::SourceLocation varEnd,
                    bool isLvalue, clang::ASTContext *ctx);

            bool operator<(const varStmtStruct &x) const;

            bool operator==(const varStmtStruct &x) const;
        };

        // set of variables in the parsed code
        std::map<std::string, std::set<std::string>> variables;

        // a map between a CFGBlock and the information of all variables in that block
        std::map<clang::CFGBlock *, std::set<varStmtStruct>> blockVariableMap;

        // a map between a variable and the list of CFGBlocks where that variable is assigned a new value
        // used for placing phi functions and renaming
        std::map<std::string, std::set<clang::CFGBlock *>> assignments;

        // map between CFGBlock and phi functions. More explained in domfrontier.h
        std::map<clang::CFGBlock *, std::list<std::pair<std::string, std::vector<std::string>>>> phiPlacements;

        // a redundant datastructure which has to be replaced- a map between CFGBlock* does not hold true after the pass
        // is completed, so to transfer the information from MainVisitor to SSAWriter, I had to map the block id to the
        // set of phi functions
        std::map<int, std::list<std::pair<std::string, std::vector<std::string>>>> blockPhiFuncMap;

        // a map between the location of a variable and its replacement
        std::map<clang::SourceLocation, std::string> varReplacementMap;


        clang::CFGStmtMap *cm;

        /**
         * Recursively traverses all the children of stmt and gets the list of declaration statements
         * @param stmt
         * @param cfg
         */
        void visitDeclStmt(clang::Stmt *stmt);

        void printDomTree(clang::DomTreeNode *node);

        // used for renaming using algorithm in Fig 12 of Cytron et al.
        int whichPred(clang::CFGBlock *X, clang::CFGBlock *Y);

        // used for renaming using algorithm in Fig 12 of Cytron et al.
        void search(clang::DomTreeNode *X, std::map<std::string, int> &C, std::map<std::string, std::stack<int>> &S);

        /**
         * Renames variables down the dominator tree
         * @param dominatorTree
         */
        void renameVars(llvm::DomTreeBase<clang::CFGBlock> *dominatorTree);

    };

    class MainFunctionConsumer : public clang::ASTConsumer {
    public:
        explicit MainFunctionConsumer(clang::ASTContext *Context) : Visitor(Context) {}

        virtual void HandleTranslationUnit(clang::ASTContext &Context) {
            Visitor.TraverseDecl(Context.getTranslationUnitDecl());
        }

        MainFunctionVisitor getVisitor() {
            return Visitor;
        }

    private:
        MainFunctionVisitor Visitor;
    };

    class MainClassAction : public clang::ASTFrontendAction {
    private:
        MainFunctionConsumer* consumer;
        std::map<std::string, std::set<std::string>>* variableMap;
        std::map<clang::SourceLocation, std::string>* varReplacementMap;
        std::map<int, std::list<std::pair<std::string, std::vector<std::string>>>>* phiPlacementMap;
        clang::SourceManager* sm;
    public:

        void setReplacementMap(std::map<clang::SourceLocation, std::string>& map) {
            varReplacementMap = & map;
        }

        void setPhiPlaceMap(std::map<int, std::list<std::pair<std::string, std::vector<std::string>>>>& map) {
            phiPlacementMap = &map;
        }

        void setVariableMap(std::map<std::string, std::set<std::string>>& map) {
            variableMap = &map;
        }

        void setSM(clang::SourceManager& SM) {
            sm = &SM;
        }

        void EndSourceFileAction() {
            *varReplacementMap = consumer->getVisitor().getVarReplacementMap();

            *phiPlacementMap = consumer->getVisitor().getBlockPhiPlacementMap();

            *variableMap = consumer->getVisitor().getVariableMap();
        }

        virtual std::unique_ptr<clang::ASTConsumer>
        CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
            consumer = new MainFunctionConsumer(&Compiler.getASTContext());
            sm = &Compiler.getSourceManager();
            return std::unique_ptr<clang::ASTConsumer>(consumer);
        }
    };
}

#endif //SSA_TRANSFORM_MAINVISITOR_H
