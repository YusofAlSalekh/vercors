#ifndef PALLAS_LOOPCONTRACTTRANSFORM_H
#define PALLAS_LOOPCONTRACTTRANSFORM_H

#include "vct/col/ast/col.pb.h"

#include "Passes/Function/FunctionBodyTransformer.h"

#include <llvm/Analysis/LoopInfo.h>
#include <llvm/IR/PassManager.h>

/**
 * Implements the transformation of loop-contracts.
 */
namespace llvm2col {
namespace col = vct::col::ast;

void transformLoopContract(llvm::Loop &llvmLoop, col::LoopContract &colContract,
                           pallas::FunctionCursor &functionCursor);

void initializeEmptyLoopContract(col::LoopContract &colContract);

bool addInvariantToContract(llvm::MDNode &invMD, llvm::Loop &llvmLoop,
                            col::LlvmLoopContract &colContract,
                            llvm::MDNode &contractLoc,
                            pallas::FunctionCursor &functionCursor);

/**
 * Build argument-expression that dereferences the value of the given alloca.
 */
void buildArgExprFromAlloca(col::LlvmFunctionInvocation &wrapperCall,
                            unsigned int argIdx, llvm::AllocaInst &llvmAlloca,
                            llvm::Function &llvmWFunc, llvm::MDNode &srcLoc,
                            pallas::FunctionCursor &functionCursor);

} // namespace llvm2col

#endif // PALLAS_LOOPCONTRACTTRANSFORM_H