#include <iostream>
#include <fstream>
#include <vector>
#include "pin.H"
using std::cerr;
using std::endl;
using std::ios;
using std::ofstream;
using std::string;
using std::vector;
#include <algorithm>

ofstream OutFile;
#define BUFFER_SIZE 64

struct robEl {
    INS inst;
    REG regDest = REG_INVALID();
    UINT32 memDest = 0;
    // hasDest: 0 = invalid, 1 = reg, 2 = mem
    int hasDest = 0;
    vector<INS> forwardsTo;
    vector<INS> forwardsFrom;
};

struct operandVal {
    // isValid: 0 = invalid, 1 = reg, 2 = mem
    int isValid = 0;
    REG regName = REG_INVALID();
    UINT32 memAddr = 0;
};

// The running count of instructions is kept here
// make it static to help the compiler optimize docount
static UINT64 forwardCount = 0;
static UINT64 iCount = 0;
vector<robEl> rob;

// This function is called before every instruction is executed
VOID checkDependency(INS ins) {
    robEl curEl;
    curEl.inst = ins;
    vector<operandVal> operandVals;

    iCount++;
    // Ensure buffer does not exceed BUFFER_SIZE
    // ROB does not include ins in EX and beyond
    if (rob.size() == BUFFER_SIZE) {
        rob.erase(rob.begin());
    }

    if ((INS_Category(ins) == XED_CATEGORY_BINARY || INS_Category(ins) == XED_CATEGORY_LOGICAL) && (INS_OperandCount(ins) <= 2)) {            
        // forwardCount++;
        for (unsigned int i = 0; i < INS_OperandCount(ins); i++) {
            operandVal newVal;
            // get dest and src (if present)
            if (INS_OperandIsReg(ins, i)) {
                newVal.isValid = 1;
                newVal.regName = INS_OperandReg(ins, i);
                newVal.memAddr = 0;
                if (i == 0) {
                    // First operand is destination. Make it the inst's destination
                    curEl.hasDest = 1;
                    curEl.regDest = INS_OperandReg(ins, i);
                    curEl.memDest = 0;
                }
             } else if (INS_OperandIsMemory(ins, i)) {
                newVal.isValid = 2;
                newVal.memAddr = INS_OperandMemoryDisplacement(ins, i) + INS_OperandMemoryBaseReg(ins, i)
                                            + INS_OperandMemoryIndexReg(ins, i) * INS_OperandMemoryScale(ins, i);
                newVal.regName = REG_INVALID();
                if (i == 0) {
                    // First operand is destination. Make it the inst's destination
                    curEl.hasDest = 2;
                    curEl.regDest = REG_INVALID();
                    curEl.memDest = INS_OperandMemoryDisplacement(ins, i) + INS_OperandMemoryBaseReg(ins, i)
                                            + INS_OperandMemoryIndexReg(ins, i) * INS_OperandMemoryScale(ins, i);
                }
            }
            operandVals.push_back(newVal);
        }
        vector<unsigned int> potentialForwardLocs(operandVals.size(), rob.size() + 1);
        vector<unsigned int> prevPotentialForwardLocs(operandVals.size(), rob.size() + 1);

        for (unsigned int i = 0; i < rob.size(); i++) {
            // Go through each operand value of cur ins and see if match any previous dest
            for (unsigned int j = 0; j < operandVals.size(); j++) {
                // std::cout << rob[i].hasDest << " " << operandVals[j].isValid << std::endl;
                if ((rob[i].hasDest == 1 && operandVals[j].isValid == 1 && rob[i].regDest == operandVals[j].regName)
                        || (rob[i].hasDest == 2 && operandVals[j].isValid == 2 && rob[i].memDest == operandVals[i].memAddr)) {
                    // Check register match
                    // For each operand, get latest used INS
                    prevPotentialForwardLocs[j] = potentialForwardLocs[j];
                    potentialForwardLocs[j] = i;
                }
            }
        }

        // Ignore all potential locs if any other operand's potential locs have RAW after the checking potential loc
        for (unsigned int i = 0; i < potentialForwardLocs.size(); i++) {
            for (unsigned int j = 0; j < prevPotentialForwardLocs.size(); j++) {
                if (i == j || potentialForwardLocs[i] == rob.size() + 1 || prevPotentialForwardLocs[j] == rob.size() + 1) {
                    continue;
                }
                if (potentialForwardLocs[i] < prevPotentialForwardLocs[j]) {
                    potentialForwardLocs[i] = rob.size() + 1;
                }
            }
        }
        
        rob.push_back(curEl);
        unsigned int curElIdx = rob.size() - 1;
        bool forwarding = false;
        unsigned int bestIdx = rob.size();

        // Bring cur INS to latest potential forward loc + 1
        // IF pot forward loc has availability (toForward size < 2)
        std::sort(potentialForwardLocs.begin(), potentialForwardLocs.end(), std::greater<int>());

        // 1. Furthest from EX first
        if (potentialForwardLocs[0] == rob.size()) {
            return;
        }
        if (potentialForwardLocs[0] == rob.size() - 2) {
            // EDGE CASE: best forward loc is latest INS in rob
            rob[curElIdx].forwardsFrom.push_back(rob[potentialForwardLocs[0]].inst);
            rob[potentialForwardLocs[0]].forwardsTo.push_back(ins);
            forwarding = true;
            forwardCount++;
        } else if (rob[potentialForwardLocs[0]].forwardsTo.size() < 2) {
            // Check if potForward INS has space to accomodate
            // Bool is true when next 2 inst has dependency but 2nd inst after does not depend on potForward INS
            bool nextInstCanBeMovedDown = false;
            for (unsigned int j = potentialForwardLocs[0] + 1; j < potentialForwardLocs[0] + 3 || j < rob.size() - 2; j++) {
                if (rob[j].forwardsFrom.size() == 0) {
                    bestIdx = std::min(j, bestIdx);
                } else if (rob[j].forwardsFrom.size() == 1) {
                    if (j == potentialForwardLocs[0] + 1) {
                        if (rob[j].forwardsFrom[0] == rob[potentialForwardLocs[0]].inst) {
                            nextInstCanBeMovedDown = true;
                        }
                    } else if (j == potentialForwardLocs[0] + 2) {
                        if (rob[j].forwardsFrom[0] == rob[potentialForwardLocs[0]].inst) {
                            nextInstCanBeMovedDown = false;
                        }
                    }
                }
            }
            if (nextInstCanBeMovedDown) {
                bestIdx = potentialForwardLocs[0] + 1;
            }

            // Since closest potForward INS has no space, we can assume forwarding not possible
            if (bestIdx == rob.size()) {
                return;
            } else {
                // have space at bestIdx
                rob[curElIdx].forwardsFrom.push_back(rob[potentialForwardLocs[0]].inst);
                rob[potentialForwardLocs[0]].forwardsTo.push_back(ins);
                robEl tmpEl = rob[curElIdx];
                rob.erase(rob.begin() + curElIdx);
                rob.insert(rob.begin() + bestIdx, tmpEl);
                forwarding = true;
                forwardCount++;
            }
        }

        // 2. Check if second forwarding exist/possible
        // If previous forwarding not performed. No point in this because there's RAW hazard if moved before that dependent ins
        if ((potentialForwardLocs[1] == rob.size()) || !forwarding || (potentialForwardLocs[0] == potentialForwardLocs[1]) || 
                (rob[potentialForwardLocs[0]].forwardsFrom.size() > 0) || (rob[potentialForwardLocs[0]].forwardsTo.size() > 1)) {
            return;
        } else {
            // If second forwarding INS has no forwardTo, and next 2 INS has no forwardFrom, then move cur INS and its previous dependent INS up
            if (rob[potentialForwardLocs[1]].forwardsTo.size() == 0) {
                for (unsigned int i = potentialForwardLocs[1] + 1; i < potentialForwardLocs[1] + 3 || i < rob.size() - 2; i++) {
                    if (rob[i].forwardsFrom.size() > 0) {
                        return;
                    }
                }
                // next 2 INS from second forwarding has no forwardTo. So move both cur ins and its previous dependent up
                rob[bestIdx].forwardsFrom.push_back(rob[potentialForwardLocs[1]].inst);
                rob[potentialForwardLocs[1]].forwardsTo.push_back(ins);
                robEl tmpEl_1 = rob[bestIdx];
                robEl tmpEl_2 = rob[potentialForwardLocs[0]];
                rob.erase(rob.begin() + bestIdx);
                rob.erase(rob.begin() + potentialForwardLocs[0]);
                rob.insert(rob.begin() + potentialForwardLocs[1] + 1, tmpEl_2);
                rob.insert(rob.begin() + potentialForwardLocs[1] + 2, tmpEl_1);
                forwardCount++;
            }
        }

        // std::cout << forwarding << curElIdx << bestIdx << std::endl;
        return;
    }
    rob.push_back(curEl);
    operandVals.clear();
}

// Pin calls this function every time a new instruction is encountered
VOID Instruction(INS ins, VOID* v)
{
    // Insert a call to docount before every instruction, no arguments are passed
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)checkDependency, IARG_UINT32, ins, IARG_END);
}

KNOB< string > KnobOutputFile(KNOB_MODE_WRITEONCE, "pintool", "o", "MyPinTool.out", "specify output file name");

// This function is called when the application exits
VOID Fini(INT32 code, VOID* v)
{
    // Write to a file since cout and cerr maybe closed by the application
    OutFile.setf(ios::showbase);
    OutFile << "Forwarding count " << forwardCount << endl;
    OutFile << "Total inst count " << iCount << endl;
    // OutFile << "Forwarding Potential " << forwardCount/iCount << endl;
    OutFile.close();
}

/* ===================================================================== */
/* Print Help Message                                                    */
/* ===================================================================== */

INT32 Usage()
{
    cerr << "This tool counts the number of dynamic instructions executed" << endl;
    cerr << endl << KNOB_BASE::StringKnobSummary() << endl;
    return -1;
}

/* ===================================================================== */
/* Main                                                                  */
/* ===================================================================== */
/*   argc, argv are the entire command line: pin -t <toolname> -- ...    */
/* ===================================================================== */

int main(int argc, char* argv[])
{
    // std::cout << "Actually started..." << std::endl;
    // Initialize pin
    if (PIN_Init(argc, argv)) return Usage();

    OutFile.open(KnobOutputFile.Value().c_str());

    // Register Instruction to be called to instrument instructions
    INS_AddInstrumentFunction(Instruction, 0);

    // Register Fini to be called when the application exits
    PIN_AddFiniFunction(Fini, 0);

    // Start the program, never returns
    PIN_StartProgram();

    return 0;
}
