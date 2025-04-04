#include "Transform/LoopContractTransform.h"
#include "Origin/OriginProvider.h"
#include "Passes/Function/FunctionDeclarer.h"
#include "Transform/Transform.h"
#include "Util/Constants.h"
#include "Util/Exceptions.h"
#include "Util/PallasDIMapping.h"
#include "Util/PallasMD.h"

#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Argument.h>
#include <llvm/IR/DebugInfoMetadata.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Metadata.h>
#include <llvm/Support/raw_ostream.h>
#include <string>

const std::string SOURCE_LOC = "Transform::LoopContractTransform";

void llvm2col::transformLoopContract(llvm::Loop &llvmLoop,
                                     col::LoopContract &colContract,
                                     pallas::FunctionCursor &functionCursor) {
    llvm::MDNode *contractMD = pallas::utils::getPallasLoopContract(llvmLoop);
    if (contractMD == nullptr) {
        initializeEmptyLoopContract(colContract);
        return;
    }

    // Get the source-location from the contract
    llvm::MDNode *contractSrcLoc =
        llvm::dyn_cast<llvm::MDNode>(contractMD->getOperand(1).get());
    if (contractSrcLoc == nullptr ||
        !pallas::utils::isWellformedPallasLocation(contractSrcLoc)) {
        pallas::ErrorReporter::addError(
            SOURCE_LOC,
            "Malformed loop contract. Expected src-location as second operand.",
            *llvmLoop.getHeader()->getParent());
        return;
    }

    col::LlvmLoopContract *colInvariant =
        colContract.mutable_llvm_loop_contract();
    colInvariant->set_allocated_origin(
        generatePallasLoopContractOrigin(llvmLoop, *contractSrcLoc));
    colInvariant->mutable_blame();

    // Check that the loop-contract contains invariants.
    if (contractMD->getNumOperands() < 3) {
        pallas::ErrorReporter::addError(
            SOURCE_LOC, "Malformed loop contract. No invariants were provided.",
            *llvmLoop.getHeader()->getParent());
        return;
    }

    // Extract invariants and add them to the contract
    unsigned int opIdx = 2;
    while (opIdx < contractMD->getNumOperands()) {
        // Cast operand into MDNode
        llvm::MDNode *invMD = llvm::dyn_cast_if_present<llvm::MDNode>(
            contractMD->getOperand(opIdx).get());
        if (invMD == nullptr) {
            pallas::ErrorReporter::addError(
                SOURCE_LOC,
                "Malformed loop-contract. Expected MDNode as operand.",
                *llvmLoop.getHeader()->getParent());
            return;
        }
        // Add invariant to contract
        if (!addInvariantToContract(*invMD, llvmLoop, *colInvariant,
                                    *contractSrcLoc, functionCursor)) {
            return;
        }
        ++opIdx;
    }
    return;
}

bool llvm2col::addInvariantToContract(llvm::MDNode &invMD, llvm::Loop &llvmLoop,
                                      col::LlvmLoopContract &colContract,
                                      llvm::MDNode &contractLoc,
                                      pallas::FunctionCursor &functionCursor) {
    pallas::FunctionAnalysisManager &fam =
        functionCursor.getFunctionAnalysisManager();
    llvm::Function *llvmParentFunc = llvmLoop.getHeader()->getParent();

    // Check wellformedness of MD-Node
    if (invMD.getNumOperands() < 2) {
        pallas::ErrorReporter::addError(
            SOURCE_LOC,
            "Malformed loop-invariant. Expected at least two operands.",
            *llvmParentFunc);
        return false;
    }

    // Extract src-location
    llvm::MDNode *srcLoc =
        llvm::dyn_cast_if_present<llvm::MDNode>(invMD.getOperand(0).get());
    if (srcLoc == nullptr ||
        !pallas::utils::isWellformedPallasLocation(srcLoc)) {
        pallas::ErrorReporter::addError(
            SOURCE_LOC,
            "Malformed loop-invariant. Expected src-location as first operand.",
            *llvmParentFunc);
        return false;
    }

    // Get wrapper-function
    auto *llvmWFunc = pallas::utils::getWrapperFromLoopInv(invMD);
    if (llvmWFunc == nullptr) {
        pallas::ErrorReporter::addError(SOURCE_LOC,
                                        "Malformed loop-invariant. Expected "
                                        "wrapper-function as second operand.",
                                        *llvmParentFunc);
        return false;
    }
    col::LlvmFunctionDefinition &colWFunc =
        fam.getResult<pallas::FunctionDeclarer>(*llvmWFunc)
            .getAssociatedColFuncDef();

    // Get DIVariables from MD
    llvm::SmallVector<llvm::DIVariable *, 8> diVars;
    unsigned int idx = 2;
    while (idx < invMD.getNumOperands()) {
        // Check that operand is a DIVariable
        auto *diVar = llvm::dyn_cast_if_present<llvm::DIVariable>(
            invMD.getOperand(idx).get());
        if (diVar == nullptr) {
            pallas::ErrorReporter::addError(
                SOURCE_LOC,
                "Malformed loop invariant. Expected DIVariable as operand.",
                *llvmParentFunc);
            return false;
        }
        diVars.push_back(diVar);
        idx++;
    }

    pallas::FDResult &colFResult =
        fam.getResult<pallas::FunctionDeclarer>(*llvmParentFunc);
    col::LlvmFunctionDefinition &colParentFunc =
        colFResult.getAssociatedColFuncDef();

    // Build call to wrapper-function
    auto *wrapperCall = new col::LlvmFunctionInvocation();
    wrapperCall->set_allocated_origin(
        llvm2col::generatePallasWrapperCallOrigin(*llvmWFunc, *srcLoc));
    wrapperCall->set_allocated_blame(new col::Blame());
    wrapperCall->mutable_ref()->set_id(colWFunc.id());

    // Add arguments to wrapper-call
    for (auto [argIdx, diVar] : llvm::enumerate(diVars)) {
        // Match DIVariables to LLVM-Values
        llvm::Value *llvmVal =
            pallas::utils::mapDIVarToValue(*llvmParentFunc, *diVar, &llvmLoop);
        if (llvmVal == nullptr) {
            pallas::ErrorReporter::addError(
                SOURCE_LOC, "Unable to map DIVariable to value.",
                *llvmParentFunc);
            return false;
        }

        // Get variables from llvm-values and build argument-expressions
        if (llvm::isa<llvm::AllocaInst>(llvmVal)) {
            llvm2col::buildArgExprFromAlloca(
                *wrapperCall, argIdx, *llvm::cast<llvm::AllocaInst>(llvmVal),
                *llvmWFunc, *srcLoc, functionCursor);
        } else if (llvm::isa<llvm::PHINode>(llvmVal) ||
                   llvm::isa<llvm::LoadInst>(llvmVal)) {
            col::Variable *colVar =
                &functionCursor.getVariableMapEntry(*llvmVal, true);
            // Local to var of phi-node
            auto *local = wrapperCall->add_args()->mutable_local();
            local->set_allocated_origin(
                llvm2col::generatePallasWrapperCallOrigin(*llvmWFunc, *srcLoc));
            local->mutable_ref()->set_id(colVar->id());
        } else if (auto *arg = llvm::dyn_cast<llvm::Argument>(llvmVal)) {
            col::Variable *colVar = &colFResult.getFuncArgMapEntry(*arg);
            auto *argExpr = wrapperCall->add_args()->mutable_local();
            argExpr->set_allocated_origin(
                llvm2col::generatePallasWrapperCallOrigin(*llvmWFunc, *srcLoc));
            argExpr->mutable_ref()->set_id(colVar->id());
        } else {
            std::string valStr;
            llvm::raw_string_ostream vStream(valStr);
            vStream << *llvmVal;
            pallas::ErrorReporter::addError(
                SOURCE_LOC,
                "Unable to map DIVariable to col-variable (Unsupported "
                "value):" +
                    vStream.str(),
                *llvmParentFunc);
            return false;
        }
    }

    // Append wrapper-call to loop-contract
    if (colContract.has_invariant()) {
        auto *oldInv = colContract.release_invariant();
        auto *newInv = colContract.mutable_invariant()->mutable_star();
        newInv->set_allocated_origin(
            generatePallasLoopContractOrigin(llvmLoop, contractLoc));
        newInv->set_allocated_left(oldInv);
        newInv->mutable_right()->set_allocated_llvm_function_invocation(
            wrapperCall);
    } else {
        colContract.mutable_invariant()->set_allocated_llvm_function_invocation(
            wrapperCall);
    }
    return true;
}

void llvm2col::initializeEmptyLoopContract(col::LoopContract &colContract) {
    col::LlvmLoopContract *invariant = colContract.mutable_llvm_loop_contract();
    col::BooleanValue *tt =
        invariant->mutable_invariant()->mutable_boolean_value();
    tt->set_value(true);
    tt->set_allocated_origin(generateLabelledOrigin("constant true"));
    invariant->set_allocated_origin(generateLabelledOrigin("constant true"));
    invariant->mutable_blame();
}

void llvm2col::buildArgExprFromAlloca(col::LlvmFunctionInvocation &wrapperCall,
                                      unsigned int argIdx,
                                      llvm::AllocaInst &llvmAlloca,
                                      llvm::Function &llvmWFunc,
                                      llvm::MDNode &srcLoc,
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
        // TODO: Set correct type for cast (i.e. is missing a pointer)
        llvm2col::transformAndSetPointerType(*expectedTy,
                                             *tVal->mutable_value());
        // llvm2col::transformAndSetType(*expectedTy, *tVal->mutable_value());
        // tVal->set_allocated_value();
        // llvm2col::transformAndSetType(*expectedTy, *tVal->mutable_value());
        local = cast->mutable_value()->mutable_local();
    } else {
        local = ptrDeref->mutable_pointer()->mutable_local();
    }

    // Local to var of alloca
    local->set_allocated_origin(
        llvm2col::generatePallasWrapperCallOrigin(llvmWFunc, srcLoc));
    local->mutable_ref()->set_id(colVar.id());
}