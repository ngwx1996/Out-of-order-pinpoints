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
#define BUFFER_SIZE 256
#define BASELINE 0

struct robEl {
    INS inst;
    REG regDest = REG_INVALID();
    UINT32 memDest = 0;
    // hasDest: 0 = invalid, 1 = reg, 2 = mem
    int hasDest = 0;
    vector<INS> forwardsTo;
    vector<INS> forwardsFrom;
    vector<INS> missedForwardsTo;
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
     if (rob.size() == BUFFER_SIZE) {
        rob.erase(rob.begin());
    }

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

    if (operandVals.size() > 0) {
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
        bool canStillForward = false;
        bool forwarding = false;

        // Bring cur INS to latest potential forward loc + 1
        // IF pot forward loc has availability (toForward size < 3)
        std::sort(potentialForwardLocs.begin(), potentialForwardLocs.end(), std::greater<int>());

        // 1. Furthest from EX first
        if (potentialForwardLocs[0] == rob.size()) {
            return;
        } else if (potentialForwardLocs[0] > rob.size() - 5) {
            // EDGE CASE: best forward loc already being forwarded by default
            rob[curElIdx].forwardsFrom.push_back(rob[potentialForwardLocs[0]].inst);
            rob[potentialForwardLocs[0]].forwardsTo.push_back(ins);
            forwardCount++;
            forwarding = true;
            if (rob[potentialForwardLocs[0]].forwardsTo.size() == 1 && rob[potentialForwardLocs[0]].forwardsFrom.size() == 0) {
                canStillForward = true;
            }
        } else if (!BASELINE && rob[potentialForwardLocs[0]].forwardsTo.size() < 3) {
            unsigned int bestIdx = rob.size();
            // Check if potForward INS has space to accomodate
            // Bool is true when next 2 inst has dependency but 2nd inst after does not depend on potForward INS            
            for (unsigned int j = potentialForwardLocs[0] + 3; j > potentialForwardLocs[0]; j--) {
                if (j > rob.size() - 2) {
                    continue;
                }
                if (rob[j].forwardsFrom.size() == 0) {
                    bestIdx = std::min(j, bestIdx);
                } else if (rob[j].forwardsTo.size() > 0) {
                    if (rob[j].forwardsTo.size() == 1 && j == potentialForwardLocs[0] + 1 && rob[j].forwardsTo[0] == rob[j + 1].inst) {
                        continue;
                    }
                    // if this spot's instruction is forwarding to another inst, reset bestIdx to prevent dislodging its forwarding.
                    bestIdx = rob.size();
                }
            }

            if (rob[potentialForwardLocs[0]].forwardsTo.size() == 0) {
                if (potentialForwardLocs[0] + 1 <= rob.size() - 3 && rob[potentialForwardLocs[0] + 1].forwardsFrom.size() == 0) {
                    if (potentialForwardLocs[0] + 2 <= rob.size() - 4 && 
                            (rob[potentialForwardLocs[0] + 2].forwardsFrom.size() == 0 || 
                            (rob[potentialForwardLocs[0] + 2].forwardsFrom.size() == 1 && rob[potentialForwardLocs[0] + 2].forwardsFrom[0] != rob[potentialForwardLocs[0] + 1].inst))) {
                        bestIdx = potentialForwardLocs[0] + 1;
                    }
                }
            }

            if (bestIdx == rob.size()) {
                rob[potentialForwardLocs[0]].missedForwardsTo.push_back(ins);
            } else {
                // have space at bestIdx
                rob[curElIdx].forwardsFrom.push_back(rob[potentialForwardLocs[0]].inst);
                rob[potentialForwardLocs[0]].forwardsTo.push_back(ins);
                robEl tmpEl = rob[curElIdx];
                rob.erase(rob.begin() + curElIdx);
                rob.insert(rob.begin() + bestIdx, tmpEl);
                forwardCount++;
                forwarding = true;
                curElIdx = bestIdx;
                if (rob[potentialForwardLocs[0]].forwardsTo.size() == 1 && rob[potentialForwardLocs[0]].forwardsFrom.size() == 0) {
                    canStillForward = true;
                } 
            }
        } else {
            rob[potentialForwardLocs[0]].missedForwardsTo.push_back(ins);
        }

        // 2. Check if second forwarding exist/possible
        if (potentialForwardLocs.size() <= 1 || (potentialForwardLocs.size() > 1 && potentialForwardLocs[1] == rob.size())) {
            return;
        }
        // Check if can still forward to next target with both cur inst and latest target back to back
        // Means next target must have space to accomdate two inst
            // Check if next target already forwarding...
        if (curElIdx > potentialForwardLocs[1] && curElIdx <= potentialForwardLocs[1] + 3) {
            rob[curElIdx].forwardsFrom.push_back(rob[potentialForwardLocs[1]].inst);
            rob[potentialForwardLocs[1]].forwardsTo.push_back(ins);
            forwardCount++;
            if (!(rob[potentialForwardLocs[1]].forwardsTo.size() == 1 && rob[potentialForwardLocs[1]].forwardsFrom.size() == 0)) {
                canStillForward = false;
            }
        } else if (forwarding && canStillForward && potentialForwardLocs[1] != potentialForwardLocs[0]) {
            if (!BASELINE && rob[potentialForwardLocs[1]].forwardsTo.size() < 2) {
                bool noForwards = true;
                for (unsigned int j = potentialForwardLocs[0] + 1; j < potentialForwardLocs[0] + 3 || j < rob.size() - 2; j++) {
                    if (rob[j].forwardsFrom.size() != 0) {
                        noForwards = false;
                    }
                }
                if (potentialForwardLocs[1] + 2 < rob.size() - 2 &&
                        rob[potentialForwardLocs[1] + 2].forwardsFrom.size() == 1 && rob[potentialForwardLocs[1] + 2].forwardsFrom[0] == rob[potentialForwardLocs[1] + 1].inst) {
                    noForwards = true;
                }
                if (noForwards) {
                    rob[curElIdx].forwardsFrom.push_back(rob[potentialForwardLocs[1]].inst);
                    rob[potentialForwardLocs[1]].forwardsTo.push_back(ins);
                    robEl tmpEl_1 = rob[curElIdx];
                    robEl tmpEl_2 = rob[potentialForwardLocs[0]];
                    rob.erase(rob.begin() + curElIdx);
                    rob.erase(rob.begin() + potentialForwardLocs[0]);
                    rob.insert(rob.begin() + potentialForwardLocs[1] + 1, tmpEl_2);
                    rob.insert(rob.begin() + potentialForwardLocs[1] + 2, tmpEl_1);
                    forwardCount++;
                    potentialForwardLocs[0] = potentialForwardLocs[1] + 1;
                    curElIdx = potentialForwardLocs[1] + 2;
                    if (rob[potentialForwardLocs[1]].forwardsTo.size() == 1 && rob[potentialForwardLocs[1]].forwardsFrom.size() == 0) {
                        canStillForward = true;
                    } else {
                        canStillForward = false;
                    }
                } else if (potentialForwardLocs[1] + 2 < rob.size() - 2 && potentialForwardLocs[1] - 1 >= 0 && rob[potentialForwardLocs[1] + 2].forwardsFrom.size() == 0 && 
                        rob[potentialForwardLocs[1] + 1].forwardsFrom.size() == 1 && rob[potentialForwardLocs[1] + 1].forwardsFrom[1] == rob[potentialForwardLocs[1] - 1].inst) {
                    rob[curElIdx].forwardsFrom.push_back(rob[potentialForwardLocs[1]].inst);
                    rob[potentialForwardLocs[1]].forwardsTo.push_back(ins);
                    robEl tmpEl_1 = rob[curElIdx];
                    robEl tmpEl_2 = rob[potentialForwardLocs[0]];
                    rob.erase(rob.begin() + curElIdx);
                    rob.erase(rob.begin() + potentialForwardLocs[0]);
                    rob.insert(rob.begin() + potentialForwardLocs[1] - 1, tmpEl_2);
                    rob.insert(rob.begin() + potentialForwardLocs[1] + 1, tmpEl_1);
                    forwardCount++;
                    potentialForwardLocs[0] = potentialForwardLocs[1] - 1;
                    curElIdx = potentialForwardLocs[1] + 1;
                    if (rob[potentialForwardLocs[1]].forwardsTo.size() == 1 && rob[potentialForwardLocs[1]].forwardsFrom.size() == 0) {
                        canStillForward = true;
                    }  else {
                        canStillForward = false;
                    }
                } else {
                    canStillForward = false;
                }
            } else {
                rob[potentialForwardLocs[1]].missedForwardsTo.push_back(ins);
                canStillForward = false;
            }
        } else {
            rob[potentialForwardLocs[1]].missedForwardsTo.push_back(ins);
            canStillForward = false;
        }

        // 3. Check if third forwarding exist/possible
        if (potentialForwardLocs.size() <= 2 || (potentialForwardLocs.size() > 2 && potentialForwardLocs[2] == rob.size())) {
            return;
        }

        if (curElIdx > potentialForwardLocs[2] && curElIdx <= potentialForwardLocs[2] + 3) {
            rob[curElIdx].forwardsFrom.push_back(rob[potentialForwardLocs[2]].inst);
            rob[potentialForwardLocs[2]].forwardsTo.push_back(ins);
            forwardCount++;
        } else if (!BASELINE && forwarding && canStillForward && potentialForwardLocs[2] != potentialForwardLocs[1]) {
            if (rob[potentialForwardLocs[2]].forwardsTo.size() == 0) {
                for (unsigned int i = potentialForwardLocs[2] + 1; i < potentialForwardLocs[2] + 3 || i < rob.size() - 2; i++) {
                    if (rob[i].forwardsFrom.size() > 0) {
                        canStillForward = false;
                        break;
                    }
                }

                if (curElIdx > potentialForwardLocs[2] && curElIdx <= potentialForwardLocs[2] + 3) {
                    rob[curElIdx].forwardsFrom.push_back(rob[potentialForwardLocs[2]].inst);
                    rob[potentialForwardLocs[2]].forwardsTo.push_back(ins);
                    forwardCount++;
                } else if (!BASELINE && canStillForward) {
                    // next 3 INS from third forwarding has no forwardFrom. So move both cur ins and its previous dependent up
                    rob[curElIdx].forwardsFrom.push_back(rob[potentialForwardLocs[2]].inst);
                    rob[potentialForwardLocs[2]].forwardsTo.push_back(ins);
                    robEl tmpEl_1 = rob[curElIdx];
                    robEl tmpEl_2 = rob[potentialForwardLocs[0]];
                    robEl tmpEl_3 = rob[potentialForwardLocs[1]];
                    rob.erase(rob.begin() + curElIdx);
                    rob.erase(rob.begin() + potentialForwardLocs[0]);
                    rob.erase(rob.begin() + potentialForwardLocs[1]);
                    rob.insert(rob.begin() + potentialForwardLocs[2] + 1, tmpEl_3);
                    rob.insert(rob.begin() + potentialForwardLocs[2] + 2, tmpEl_2);
                    rob.insert(rob.begin() + potentialForwardLocs[2] + 3, tmpEl_1);
                    forwardCount++;
                } else {
                    // move last target down if possible
                    if (curElIdx + 1 == potentialForwardLocs[0] && potentialForwardLocs[0] + 1 == potentialForwardLocs[1]) {
                        if (rob[potentialForwardLocs[2]].missedForwardsTo.size() == 0 && rob[potentialForwardLocs[1] - 1].forwardsTo.size() == 0) {
                            rob[curElIdx].forwardsFrom.push_back(rob[potentialForwardLocs[2]].inst);
                            rob[potentialForwardLocs[2]].forwardsTo.push_back(ins);
                            robEl tmpEl_1 = rob[potentialForwardLocs[2]];
                            rob.insert(rob.begin() + potentialForwardLocs[1] + 1, tmpEl_1);
                            rob.erase(rob.begin() + potentialForwardLocs[2]);
                            forwardCount++;
                        }
                    } else {
                        rob[potentialForwardLocs[2]].missedForwardsTo.push_back(ins);
                    }
                }
            }
        }

        if (!BASELINE && !forwarding && curElIdx == rob.size() - 1) {
            int moveToEndCount = 0;
            for (unsigned int j = 0; j < potentialForwardLocs.size(); j++) {
                if (potentialForwardLocs[j] == rob.size()) {
                    break;
                }
                if (rob[potentialForwardLocs[j]].forwardsTo.size() == 0
                        && rob[potentialForwardLocs[j]].forwardsFrom.size() == 0 && rob[potentialForwardLocs[j]].missedForwardsTo.size() == 0) {
                    moveToEndCount++;
                    rob[curElIdx].forwardsFrom.push_back(rob[potentialForwardLocs[j]].inst);
                    rob[potentialForwardLocs[j]].forwardsTo.push_back(ins);
                    robEl tmpEl_1 = rob[potentialForwardLocs[j]];
                    rob.insert(rob.begin() + curElIdx - moveToEndCount, tmpEl_1);
                    rob.erase(rob.begin() + potentialForwardLocs[j]);
                    forwardCount++;
                }
            }
        }

        operandVals.clear();
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

KNOB< string > KnobOutputFile(KNOB_MODE_WRITEONCE, "pintool", "o", "RobScan.out", "specify output file name");

// This function is called when the application exits
VOID Fini(INT32 code, VOID* v)
{
    // Write to a file since cout and cerr maybe closed by the application
    OutFile.setf(ios::showbase);
    OutFile << "Forwarding count " << forwardCount << endl;
    OutFile << "Total inst count " << iCount << endl;
    OutFile << "Forwarding Potential " << float(forwardCount)/float(iCount) << endl;
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
