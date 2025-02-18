#ifndef PALLAS_INTRINSICSTRANSFORM_H
#define PALLAS_INTRINSICSTRANSFORM_H
#include "Passes/Function/FunctionBodyTransformer.h"

#include <llvm/IR/Instructions.h>

namespace llvm2col {
namespace col = vct::col::ast;

void transformIntrinsic(llvm::CallInst &callInstruction,
                        col::LlvmBasicBlock &colBlock,
                        pallas::FunctionCursor &funcCursor);

/**
 * Transform call to the @llvm.trap()-intrinsic
 */
void transformTrap(llvm::CallInst &callInstruction,
                   col::LlvmBasicBlock &colBlock,
                   pallas::FunctionCursor &funcCursor);

} // namespace llvm2col

#endif // PALLAS_INTRINSICSTRANSFORM_H
