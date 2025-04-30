#include <set>
#include <map>
#include <vector>
#include <iostream>
#include <cstdio>
#include <ranges>
#include <numeric>
#include <cinttypes>
#include <vector>
#include <algorithm>
#include <cmath>
#include <iostream>
#include <iomanip>
#include <string>

#include "library.h"
#include "binaryninjaapi.h"

#include "highlevelilinstruction.h"

#include "patterns/examples/llil_add.hpp"
#include "patterns/examples/mlil_add.hpp"

#include "highlevelilinstruction.h"

using namespace BinaryNinja;
using namespace std;


void PatchFunction(BinaryView* bv, Function* func) {
    std::vector<BasicBlock*> cffHeads;

    for (auto& block : func->GetHighLevelIL()->GetBasicBlocks()) {
        int dominatedEdges = 0;
        for (auto& edge : block->GetIncomingEdges()) {
            if (edge.target->GetDominatorTreeChildren().count(block))
                dominatedEdges++;
        }
        if (dominatedEdges >= 3)
            cffHeads.push_back(block);
    }

    if (cffHeads.empty()) return;
    BasicBlock* cffHead = cffHeads[0];

    std::set<BasicBlock*> blocks;
    std::vector<BasicBlock*> toVisit = {cffHead};
    while (!toVisit.empty()) {
        BasicBlock* block = toVisit.back();
        toVisit.pop_back();
        for (auto& edge : block->GetIncomingEdges()) {
            BasicBlock* candidateBlock = edge.target;
            if (cffHead->GetDominatorTreeChildren().count(candidateBlock) && blocks.count(candidateBlock) == 0) {
                blocks.insert(candidateBlock);
                toVisit.push_back(candidateBlock);
            }
        }
    }

    std::set<HighLevelILInstruction> conditions;
    for (auto* block : blocks) {
        for (auto& edge : block->GetIncomingEdges()) {
            auto condition = func->GetHighLevelIL()->GetInstruction(edge.target->GetEnd() - 1);
            if (condition.operation == HLIL_IF)
                conditions.insert(condition);
        }
    }

    std::map<Variable, int> varCounts;
    for (const auto& condition : conditions) {
        for (const auto& var : condition.GetOperands()[0].GetVariable()) {
            varCounts[var]++;
        }
    }

    auto targetVar = std::max_element(varCounts.begin(), varCounts.end(),
        [](const auto& a, const auto& b) { return a.second < b.second; })->first;

    std::map<uint64_t, BasicBlock*> codeLookup;
    for (const auto& condition : conditions) {
        if (condition.operation != HLIL_CMP_E)
            throw std::runtime_error("Unsupported condition type");

        auto trueBranch = condition.GetTrueBranch<BasicBlock>();
        auto constValue = condition.GetOperands()[1].GetConstant();
        if (!constValue)
            throw std::runtime_error("No constant value found");

        codeLookup[constValue->GetValue()] = trueBranch->GetBasicBlock();
    }

    std::map<uint64_t, BasicBlock*> blockExits;
    for (auto* block : blocks) {
        for (size_t i = block->GetStart(); i < block->GetEnd(); i++) {
            auto instr = func->GetHighLevelIL()->GetInstruction(i);
            if (instr.operation == HLIL_ASSIGN && instr.GetOperands()[0].IsVariable(targetVar)) {
                blockExits[instr.GetOperands()[1].GetConstant()->GetValue()] = block;
            }
        }
    }

    for (const auto& [code, block] : blockExits) {
        auto asmBlock = func->GetBasicBlockAt(block->GetStart());
        auto lastInstr = asmBlock->GetInstructionText().back();
        if (lastInstr[0].m_text != "jmp")
            throw std::runtime_error("Block does not end with jmp");

        auto address = lastInstr[0].m_address;
        auto length = asmBlock->GetEnd() - address;

        auto outBlock = codeLookup[code];
        auto outAsmBlock = func->GetBasicBlockAt(outBlock->GetStart());
        auto outAddress = outAsmBlock->GetStart();

        auto bytecode = bv->Read(address, length);
        std::vector<uint8_t> newBytecode;

        if (length == 2 && bytecode[0] == 0xEB) {
            int8_t delta = outAddress - asmBlock->GetEnd();
            if (std::abs(delta) > 0x7F) continue;
            newBytecode = {0xEB, static_cast<uint8_t>(delta)};
        } else if (length == 5 && bytecode[0] == 0xE9) {
            int32_t delta = outAddress - asmBlock->GetEnd();
            newBytecode = {0xE9, static_cast<uint8_t>(delta & 0xFF), static_cast<uint8_t>((delta >> 8) & 0xFF),
                           static_cast<uint8_t>((delta >> 16) & 0xFF), static_cast<uint8_t>((delta >> 24) & 0xFF)};
        } else {
            continue;
        }

        bv->Write(address, newBytecode);
    }
}

void MergeBasicBlocks(const Ref<AnalysisContext>& analysisContext) {
    const Ref<Function> func = analysisContext->GetFunction();
    const Ref<MediumLevelILFunction> il = func->GetMediumLevelIL();

    if (!il) {
        printf("\tDoes not have MLIL\n\n");
        return;
    }

    // hardcoded for testing purposes since we are just testing basic blocks feature
    if (func->GetSymbol()->GetFullName() == "simple_branch") {
        printf("[TEST] %s\n", func->GetSymbol()->GetFullName().c_str());

        std::vector<Ref<BasicBlock>> blocks = il->GetBasicBlocks();
        for (size_t i = 0; i < blocks.size(); ++i) {
            Ref<BasicBlock> block = blocks[i];
            printf("[TEST] Block start: %" PRIx64 ", end: %" PRIx64 "\n", block->GetStart(), block->GetEnd());

            // if (block->GetOutgoingEdges().size() == 1) {
            //     Ref<BasicBlock> targetBlock = block->GetOutgoingEdges()[0].target;
            //     printf("[TEST] Target block start: %" PRIx64 ", end: %" PRIx64 "\n", targetBlock->GetStart(), targetBlock->GetEnd());
            //
            //     for (size_t instrIndex = targetBlock->GetStart(); instrIndex < targetBlock->GetEnd(); ++instrIndex) {
            //         MediumLevelILInstruction instr = (*il)[instrIndex];
            //         printf("[TEST] %lu\n", instr.exprIndex);
            //         il->AddInstruction(instr.exprIndex);
            //     }
            //
            //     blocks.erase(blocks.begin() + i + 1);
            //     --i;
            // }
        }

        il->GenerateSSAForm();
    }
}

extern "C"
{
    BINARYNINJAPLUGIN uint32_t CorePluginABIVersion() { return BN_CURRENT_CORE_ABI_VERSION; }

    void RegisterMBAPatches() {
        LLIL_ADD_Searcher* llilAddSearcher = new LLIL_ADD_Searcher();
        Ref<Workflow> customLLILPatcherWorkflow = Workflow::Instance("core.function.baseAnalysis")->Clone("LLILPatcherWorkflow");
        customLLILPatcherWorkflow->RegisterActivity(new Activity("extension.llilpatcher", [llilAddSearcher](const Ref<AnalysisContext>& context) {
            llilAddSearcher->SearchLLIL(context);
        }));

        customLLILPatcherWorkflow->Insert("core.function.generateMediumLevelIL", "extension.llilpatcher");
        Workflow::RegisterWorkflow(customLLILPatcherWorkflow,
            R"#({
                "title" : "Test4",
                "description" : "This analysis stands in as an example to demonstrate Binary Ninja's extensible analysis APIs.",
                "targetType" : "function"
            })#"
        );

        MLIL_ADD_Searcher* mlilAddSearcher = new MLIL_ADD_Searcher();
        Ref<Workflow> customMLILPatcherWorkflow = Workflow::Instance("core.function.baseAnalysis")->Clone("MLILPatcherWorkflow");
        customMLILPatcherWorkflow->RegisterActivity(new Activity("extension.mlilpatcher", [mlilAddSearcher](const Ref<AnalysisContext>& context) {
            mlilAddSearcher->SearchMLIL(context);
        }));

        customMLILPatcherWorkflow->Insert("core.function.generateHighLevelIL", "extension.mlilpatcher");
        Workflow::RegisterWorkflow(customMLILPatcherWorkflow,
            R"#({
                "title" : "Test7",
                "description" : "This analysis stands in as an example to demonstrate Binary Ninja's extensible analysis APIs.",
                "targetType" : "function"
            })#"
        );
    }

    int CalcCyclomaticComplexity(Ref<Function> func) {
        std::vector<Ref<BasicBlock>> basicBlocks = func->GetBasicBlocks();
        int numOfBlocks = basicBlocks.size();
        int numOfEdges = 0;

        for (const auto& block : basicBlocks) {
            numOfEdges += block->GetOutgoingEdges().size();
        }

        return numOfEdges - numOfBlocks + 2;
    }

    std::set<Ref<BasicBlock>> getDominatedBy(const Ref<BasicBlock>& dominator) {
        std::set<Ref<BasicBlock>> result;
        std::vector<Ref<BasicBlock>> worklist = { dominator };

        while (!worklist.empty()) {
            Ref<BasicBlock> block = worklist.back();
            worklist.pop_back();

            result.insert(block);
            for (const auto& child : block->GetDominatorTreeChildren()) {
                if (!result.count(child))
                    worklist.push_back(child);
            }
        }

        return result;
    }

    double CalcFlatteningScore(const Ref<Function>& function) {
        double score = 0.0;
        std::vector<Ref<BasicBlock>> blocks = function->GetBasicBlocks();

        for (const auto& block : blocks) {
            std::set<Ref<BasicBlock>> dominated = getDominatedBy(block);

            bool hasBackEdge = false;
            for (const auto& edge : block->GetIncomingEdges()) {
                if (dominated.count(edge.target)) {
                    hasBackEdge = true;
                    break;
                }
            }

            if (!hasBackEdge)
                continue;
            score = std::max(score, static_cast<double>(dominated.size()) / static_cast<double>(blocks.size()));
        }

        return score;
    }

    Variable GetMostAssignedVar(const Ref<Function>& func) {
        std::map<Variable, size_t> varAssignementCount;

        Ref<HighLevelILFunction> hlil = func->GetHighLevelIL();
        if(!hlil)
          throw std::runtime_error("No HLIL available for this function");

        for (const auto& var : hlil->GetVariables()) {
          auto defs = hlil->GetVariableDefinitions(var);
          varAssignementCount[var] = defs.size();
        }

        if (varAssignementCount.empty())
            throw std::runtime_error("No variables found");

        auto mostUsed = std::max_element(
            varAssignementCount.begin(), varAssignementCount.end(),
            [](const auto& a, const auto& b) {
              return a.second < b.second;
            }
        );

        return mostUsed->first;
    }

    std::vector<Variable> GetVarDependencies(const Ref<HighLevelILFunction>& hlilFunc, const Variable& var)
    {
        std::vector<Variable> deps;
        std::set<size_t> defines = hlilFunc->GetVariableDefinitions(var);

        for (const auto& def : defines) {
            // ToDo : Lionel a dit fusionne les basicblocks, ignore les etc
            // L'analyse sera là pour plus tard
        }

        return deps;
    }

    void PatchJumps(AnalysisContext* analysisContext) {
        Ref<Function> function = analysisContext->GetFunction();
        std::string funcAddr = std::to_string(function->GetStart());

        auto mlil = function->GetMediumLevelIL();
        
    }

    void RegisterCFFPatches() {
        PluginCommand::RegisterForFunction("eshard\\CFF\\Cyclomatic complexity", "Compute cyclomatic complexity", [](BinaryView* view, Function *func) {
              int complexity = CalcCyclomaticComplexity(func);
              LogInfo("Cyclomatic complexity of %s %d", func->GetSymbol()->GetFullName().c_str(), complexity);
        });

        PluginCommand::Register("eshard\\CFF\\Complex Functions", "Find complex functions", [](BinaryView* view) {
            std::vector<Ref<Function>> funcs = view->GetAnalysisFunctionList();

            std::sort(funcs.begin(), funcs.end(), [](const Ref<Function>& a, const Ref<Function>& b) {
                return CalcCyclomaticComplexity(a) < CalcCyclomaticComplexity(b);
            });

            size_t bound = static_cast<size_t>(std::ceil(funcs.size() * 0.10));
            for (auto it = funcs.rbegin(); it != funcs.rbegin() + bound; ++it) {
                std::cout << "0x" << std::hex << (*it)->GetStart() << ": "
                          << std::dec << CalcCyclomaticComplexity(*it) << std::endl;
            }
        });

        PluginCommand::RegisterForFunction("eshard\\CFF\\Flattening score", "Compute flattening score", [](BinaryView* view, Function* func) {
            double score = CalcFlatteningScore(func);
            LogInfo("Flattening score of %s: %.2f", func->GetSymbol()->GetFullName().c_str(), score);
        });

        PluginCommand::RegisterForFunction("eshard\\CFF\\Most Assigned Var", "Find the most assigned variable in HLIL", [](BinaryView* view, Function* func) {
            Variable var = GetMostAssignedVar(func);
            LogInfo("Most assigned var (probably the state variable) is %s", func->GetVariableName(var).c_str());
        });

        PluginCommand::RegisterForFunction("eshard\\CFF\\Var dependencies", "Get var dependencies of the most assigned var", [](BinaryView* view, Function* func) {
            auto hlil = func->GetHighLevelIL();
            if (!hlil) {
                LogWarn("No HLIL available for this function.");
                return;
            }

            Variable mostAssignedVar = GetMostAssignedVar(func);
            LogInfo("mostAssignedVar: %s", func->GetVariableName(mostAssignedVar).c_str());

            std::vector<Variable> dependencies = GetVarDependencies(hlil, mostAssignedVar);
            for (const auto& dep : dependencies) {
                LogInfo("Dependency: %s", func->GetVariableName(dep).c_str());
            }
        });
    }
    BINARYNINJAPLUGIN bool CorePluginInit()
    {
        PluginCommand::Register("eshard\\All actvities", "Print all activities", [](BinaryView* view) {
            const Ref<Workflow> defaultWf = Workflow::Instance("core.function.baseAnalysis");
            for (const auto& activity : defaultWf->GetSubactivities()) {
                LogInfo("Activity: %s", activity.c_str());
            }
        });

        RegisterMBAPatches();
        RegisterCFFPatches();

        Ref<Workflow> instructionInsertion = Workflow::Instance("core.function.baseAnalysis")->Clone("instructionInsertionWorkflow");
        instructionInsertion->RegisterActivity(new Activity("extension.instructionInsertion", [](const Ref<AnalysisContext>& context) {
            Ref<Function> func = context->GetFunction();
            auto mlil = func->GetMediumLevelIL();
        
            for (const auto& block : mlil->GetBasicBlocks()) {
                mlil->PrepareToCopyBlock(block);
                for (size_t instrIdx = block->GetStart(); instrIdx < block->GetEnd(); instrIdx++) {
                    
                }
            }
        
            mlil->GenerateSSAForm();
        }));

        Ref<Workflow> customMergeBasicBlocksWorkflow = Workflow::Instance("core.function.baseAnalysis")->Clone("MergeBasicBlocksWorkflow");
        customMergeBasicBlocksWorkflow->RegisterActivity(new Activity("extension.mergebasicblocks", [](const Ref<AnalysisContext>& context) {
            MergeBasicBlocks(context);
        }));

        customMergeBasicBlocksWorkflow->Insert("core.function.generateHighLevelIL", "extension.mergebasicblocks");
        Workflow::RegisterWorkflow(customMergeBasicBlocksWorkflow,
            R"#({
                "title" : "Merge Basic Blocks",
                "description" : "This workflow merges basic blocks in the medium level IL.",
                "targetType" : "function"
            })#"
        );

        PluginCommand::Register("Patch CFF", "Patch code flow flattening", [](BinaryView* bv) {
            for (auto& func : bv->GetAnalysisFunctions()) {
                PatchFunction(bv, func);
            }
        });

        return true;
    }
}