#include "Transform/Instruction/IntrinsicsTransform.h"
#include "Origin/OriginProvider.h"
#include "Transform/BlockTransform.h"
#include "Transform/Transform.h"
#include "Util/BlockUtils.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/Intrinsics.h>

const std::string SOURCE_LOC = "Transform::Instruction::Intrinsics";

void llvm2col::transformIntrinsic(llvm::CallInst &callInstruction,
                                  col::LlvmBasicBlock &colBlock,
                                  pallas::FunctionCursor &funcCursor) {
    llvm::Function *intrFunc = callInstruction.getCalledFunction();
    switch (intrFunc->getIntrinsicID()) {
    case llvm::Intrinsic::trap:
        transformTrap(callInstruction, colBlock, funcCursor);
        break;
    case llvm::Intrinsic::expect:
        transformExpect(callInstruction, colBlock, funcCursor);
        break;
    case llvm::Intrinsic::dbg_value:
    case llvm::Intrinsic::dbg_declare:
    case llvm::Intrinsic::dbg_assign:
        // Ignore debug-intrinsics
        break;
    default:
        reportUnsupportedOperatorError(SOURCE_LOC, callInstruction);
    }

    // TODO: Deal with more intrinsic functions
}

void llvm2col::transformTrap(llvm::CallInst &callInstruction,
                             col::LlvmBasicBlock &colBlock,
                             pallas::FunctionCursor &funcCursor) {
    // Transform @llvm.trap() --> assert false
    col::Block &body = pallas::bodyAsBlock(colBlock);
    col::VctAssert *a = body.add_statements()->mutable_vct_assert();
    a->set_allocated_blame(new col::Blame());
    a->set_allocated_origin(
        llvm2col::generateSingleStatementOrigin(callInstruction));
    col::BooleanValue *falseConst = a->mutable_res()->mutable_boolean_value();
    falseConst->set_value(false);
    falseConst->set_allocated_origin(
        llvm2col::generateSingleStatementOrigin(callInstruction));
}

void llvm2col::transformExpect(llvm::CallInst &callInstruction,
                               col::LlvmBasicBlock &colBlock,
                               pallas::FunctionCursor &funcCursor) {
    // Transform %x2 = call XXX @llvm.expect.XXX(%x1, YYY) --> x2 = x1;
    col::Assign &assignment = funcCursor.createAssignmentAndDeclaration(
        callInstruction, colBlock);
    // auto *assignExpr = assignment.mutable_value();  
    llvm2col::transformAndSetExpr(funcCursor, callInstruction,
        *callInstruction.getArgOperand(0),
        *assignment.mutable_value());                      
}
