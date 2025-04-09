#ifndef PALLAS_DIMAPPING_H
#define PALLAS_DIMAPPING_H

#include <llvm/ADT/ArrayRef.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/IR/DebugInfoMetadata.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Value.h>

/**
 * Utility-functions for mapping debug-info to llvm instructions.
 */
namespace pallas::utils {

/**
 * Returns all dbg-variable intrinsics in the given function that refer to
 * the diven DILocalVariable.
 */
llvm::SmallVector<llvm::DbgVariableIntrinsic *>
getIntrinsicsForDIVar(llvm::Function &f, llvm::DILocalVariable &diVar);

/**
 * If the given ArrayRef contains exactly one DbgDeclareInst, return a pointer
 * to this DbgDeclare. Otherwise, a nullpointer is returned.
 */
llvm::DbgDeclareInst *
getUniqueDbgDeclare(llvm::ArrayRef<llvm::DbgVariableIntrinsic *> intrinsics);

/**
 * Function that attempts to map a given DIVariable to a corresponding
 * llvm-value.
 * The mapping assumes that the resulting value will be used in a loop
 * invariant. The mapping-process uses the following steps:
 * - Try to map the DIVariable to a value through a unique dbg.declare
 *   intrinsic. If this succeeds, return.
 * - Try to map the DIVariable to a value through a unique dbg.value intrinsic.
 *   If this succeeds, return.
 * - Try to map the DIVariable to a value by finding a unique
 *   dbg.value-intrinsic that refers to a phi-node in the header-block of the
 *   given loop. If this succeeds, return.
 * - Return nullptr
 */
llvm::Value *mapDIVarToValue(llvm::Function &f, llvm::DIVariable &diVar,
                             llvm::Loop *llvmLoop);

} // namespace pallas::utils

#endif // PALLAS_DIMAPPING_H
