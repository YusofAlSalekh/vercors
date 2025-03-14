#include "Origin/OriginProvider.h"
#include "Transform/SpecStatementTransform.h"
#include "Util/Exceptions.h"
#include "Util/PallasMD.h"

#include <llvm/IR/DebugInfoMetadata.h>
#include <llvm/IR/Metadata.h>
#include <string>

const std::string SOURCE_LOC = "Transform::SpecStatementTransform";

void llvm2col::transformSpecStmntBlock(llvm::MDNode &llvmSpecBlock,
                                       llvm::Instruction &llvmInstr,
                                       col::LlvmBasicBlock &colBlock,
                                       pallas::FunctionCursor &functionCursor) {
    // Deconstruct the MD-Node
    if (llvmSpecBlock.getNumOperands() < 2) {
        pallas::ErrorReporter::addError(
            SOURCE_LOC,
            "Malformed specification block. (Expected at least two operands)",
            llvmInstr);
        return;
    }
    // Src-Location
    auto *srcLoc = llvm::dyn_cast<llvm::MDNode>(llvmSpecBlock.getOperand(0).get());
    if (!pallas::utils::isWellformedPallasLocation(srcLoc)) {
        pallas::ErrorReporter::addError(SOURCE_LOC,
                                        "Malformed specification block. "
                                        "(Expected location as first operand)",
                                        llvmInstr);
        return;
    }

    // Statements
    for (auto idx = 1; idx < llvmSpecBlock.getNumOperands(); ++idx) {
        const llvm::MDOperand &op = llvmSpecBlock.getOperand(idx);
        if (auto *stmnt = llvm::dyn_cast_if_present<llvm::MDNode>(op.get())) {
            transformSpecStmnt(*stmnt, llvmInstr, colBlock, functionCursor);
        } else {
            pallas::ErrorReporter::addError(
                SOURCE_LOC, "Malformed specification block.", llvmInstr);
            return;
        }
    }
}

namespace {
void printSpecStmntError(llvm::Instruction &inst, std::string msg) {
    pallas::ErrorReporter::addError(SOURCE_LOC,
                                    "Malformed spec-statement: " + msg, inst);
}
} // namespace

void llvm2col::transformSpecStmnt(llvm::MDNode &specStmnt,
                                  llvm::Instruction &llvmInstr,
                                  col::LlvmBasicBlock &colBlock,
                                  pallas::FunctionCursor &functionCursor) {
    // Deconstruct the MD-Node
    if (specStmnt.getNumOperands() < 3) {
        printSpecStmntError(llvmInstr, "Expected at least three operands");
        return;
    }

    // Statement-type
    auto *typeStrMD = dyn_cast<llvm::MDString>(specStmnt.getOperand(0).get());
    if (typeStrMD == nullptr) {
        printSpecStmntError(llvmInstr, "First operand should be a MDString");
        return;
    }

    // Src-location
    auto *srcLoc = llvm::dyn_cast<llvm::MDNode>(specStmnt.getOperand(1).get());
    if (!pallas::utils::isWellformedPallasLocation(srcLoc)) {
        printSpecStmntError(llvmInstr,
                            "Expected src-location as second operand");
        return;
    }

    // Wrapper-function
    auto *llvmWFunc = pallas::utils::getWrapperFunc(specStmnt.getOperand(2));
    if (llvmWFunc == nullptr) {
        printSpecStmntError(llvmInstr,
                            "Expected wrapper-function as third operand");
        return;
    }
    auto &fam = functionCursor.getFunctionAnalysisManager();
    col::LlvmFunctionDefinition &colWFunc =
        fam.getResult<pallas::FunctionDeclarer>(*llvmWFunc)
            .getAssociatedColFuncDef();

    // DI-Variables
    llvm::SmallVector<llvm::DIVariable *> diVars;
    for (auto idx = 3; idx < specStmnt.getNumOperands(); ++idx) {
        auto *diVar = llvm::dyn_cast_if_present<llvm::DIVariable>(
            specStmnt.getOperand(idx).get());
        if (diVar == nullptr) {
            printSpecStmntError(llvmInstr, "Expected DIVariable as operand");
            return;
        }
        diVars.push_back(diVar);
    }

    // Build call to wrapper-function
    auto *wCall = new col::LlvmFunctionInvocation();
    wCall->set_allocated_origin(
        llvm2col::generatePallasWrapperCallOrigin(*llvmWFunc, *srcLoc));
    wCall->set_allocated_blame(new col::Blame());
    wCall->mutable_ref()->set_id(colWFunc.id());

    // Add arguments to wrapper-call
    for (auto [argIdx, diVar] : llvm::enumerate(diVars)) {
        // Match DIVariables to LLVM-Values
        /*
        llvm::Value *llvmVal = nullptr;
        pallas::utils::mapDIVarToValue(llvmInstr, *diVar);
        if (llvmVal == nullptr) {
            printSpecStmntError(llvmInstr, "Unable to map DIVariable");
            return;
        }
        */

        // TODO: Build Arg-Expr, similar to LoopContractTransform
        // Needs to be extended to more instructions, as dbg.value no longer 
        // only points to phi-nodes.
    }
    // TODO: Implement the actual transformation

    // Build Assume or Assert node
    // TOOD: Implement
}
