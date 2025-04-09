
#include "Util/PallasWrapperUtils.h"
#include "Origin/OriginProvider.h"
#include "Transform/Transform.h"

#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Type.h>

namespace pallas::utils {
namespace col = vct::col::ast;

bool hasDiExpression(llvm::DbgVariableIntrinsic &intr) {
    return intr.getExpression() != nullptr &&
           intr.getExpression()->getNumElements() != 0;
}

void buildArgExprFromAlloca(col::LlvmFunctionInvocation &wrapperCall,
                            unsigned int argIdx, llvm::AllocaInst &llvmAlloca,
                            llvm::Function &llvmWFunc, llvm::MDNode &srcLoc,
                            pallas::FunctionCursor &functionCursor) {
    col::Variable &colVar =
        functionCursor.getVariableMapEntry(llvmAlloca, false);
    // Ptr deref
    auto *ptrDeref = wrapperCall.add_args()->mutable_deref_pointer();
    ptrDeref->set_allocated_origin(
        llvm2col::generatePallasWrapperCallOrigin(llvmWFunc, srcLoc));
    ptrDeref->set_allocated_blame(new col::Blame());

    // Cast, if type is packed struct with single element
    auto *structTy =
        llvm::dyn_cast<llvm::StructType>(llvmAlloca.getAllocatedType());
    llvm::Type *expectedTy = llvmWFunc.getArg(argIdx)->getType();
    bool isTrivialStruct = structTy != nullptr && structTy->isPacked() &&
                           structTy->getNumElements() == 1;

    col::Local *local = nullptr;
    if (structTy != expectedTy && isTrivialStruct &&
        structTy->getElementType(0) == expectedTy) {
        auto *cast = ptrDeref->mutable_pointer()->mutable_cast();
        cast->set_allocated_origin(
            llvm2col::generatePallasWrapperCallOrigin(llvmWFunc, srcLoc));
        col::TypeValue *tVal = cast->mutable_type_value()->mutable_type_value();
        tVal->set_allocated_origin(
            llvm2col::generatePallasWrapperCallOrigin(llvmWFunc, srcLoc));
        llvm2col::transformAndSetPointerType(*expectedTy,
                                             *tVal->mutable_value());
        local = cast->mutable_value()->mutable_local();
    } else {
        local = ptrDeref->mutable_pointer()->mutable_local();
    }

    // Local to var of alloca
    local->set_allocated_origin(
        llvm2col::generatePallasWrapperCallOrigin(llvmWFunc, srcLoc));
    local->mutable_ref()->set_id(colVar.id());
}

bool buildArgExprFromDbgValue(col::LlvmFunctionInvocation &wrapperCall,
                              unsigned int argIdx, llvm::DbgValueInst &dbgVal,
                              llvm::Function &llvmWFunc, llvm::MDNode &srcLoc,
                              pallas::FunctionCursor &functionCursor,
                              llvm::Function &llvmParentFunc) {
    if (hasDiExpression(dbgVal)) {
        return false;
    }
    auto *llvmValue = dbgVal.getValue();

    col::Variable *colVar = nullptr;
    if (auto *arg = llvm::dyn_cast<llvm::Argument>(llvmValue)) {
        auto &fam = functionCursor.getFunctionAnalysisManager();
        auto &colFResult =
            fam.getResult<pallas::FunctionDeclarer>(llvmParentFunc);
        colVar = &colFResult.getFuncArgMapEntry(*arg);
    } else {
        colVar = &functionCursor.getVariableMapEntry(*llvmValue, true);
    }
    auto *argExpr = wrapperCall.add_args()->mutable_local();
    argExpr->set_allocated_origin(
        llvm2col::generatePallasWrapperCallOrigin(llvmWFunc, srcLoc));
    argExpr->mutable_ref()->set_id(colVar->id());
    return true;
}

llvm::DbgValueInst *
getClosestDbgValue(llvm::SmallVector<llvm::DbgVariableIntrinsic *> &intrinsics,
                   llvm::Instruction &llvmInstr) {
    /* If this approach is not strong enough, an alternative approach would be
     * to use the dominator-tree to find the dbg.value that dominates the
     * llvmInstr but non of the other intrinsics.
     */

    // Build set of the llvm.value intrinsics
    llvm::SmallPtrSet<llvm::DbgValueInst *, 8> dbgValues;
    for (auto *intr : intrinsics) {
        if (auto *value = llvm::dyn_cast<llvm::DbgValueInst>(intr)) {
            // TODO: Also check that the intrinsic dominates the instruction
            dbgValues.insert(value);
        }
    }

    // Walk backwards through the instructions until one of the
    // dbg.value intrinsics is encountered.
    llvm::Instruction *currentInstr = &llvmInstr;
    while (
        currentInstr != nullptr &&
        !(llvm::isa<llvm::DbgValueInst>(currentInstr) &&
          dbgValues.contains(llvm::cast<llvm::DbgValueInst>(currentInstr)))) {
        // Try to go to the preceeding instruction
        if (llvm::Instruction *prevInst = currentInstr->getPrevNode()) {
            // Still in the same basic block
            currentInstr = prevInst;
        } else if (llvm::BasicBlock *prevBlock =
                       currentInstr->getParent()->getSinglePredecessor()) {
            // Try to go to the next instruction in the preceeding basic block
            // This only works if there is exactly one preceeding block
            currentInstr = prevBlock->getTerminator();
        } else {
            // No unique predecessor
            currentInstr = nullptr;
        }
    }

    if (auto *dbgValue =
            llvm::dyn_cast_if_present<llvm::DbgValueInst>(currentInstr)) {
        return dbgValues.contains(dbgValue) ? dbgValue : nullptr;
    } else {
        return nullptr;
    }
}
} // namespace pallas::utils