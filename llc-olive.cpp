/* ###########################################################
Assignment 6

Venkata Koppula, Jin Zhang

Note to self: Doubtful points marked as 'NOTE'

########################################################### */



#include <map>
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/Triple.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/CodeGen/CommandFlags.h"
#include "llvm/CodeGen/LinkAllAsmWriterComponents.h"
#include "llvm/CodeGen/LinkAllCodegenComponents.h"
#include "llvm/CodeGen/MIRParser/MIRParser.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/IRPrintingPasses.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/MC/SubtargetFeature.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PluginLoader.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetSubtargetInfo.h"
#include <memory>
#include <queue>
#include <string.h>
#include "sample4.h"


using namespace llvm;
// General options for llc.  Other pass-specific options are specified
// within the corresponding llc passes, and target-specific options
// and back-end code generation options are specified with the target machine.
//
static cl::opt<std::string>
InputFilename(cl::Positional, cl::desc("<input bitcode>"), cl::init("-"));

static cl::opt<std::string>
OutputFilename("o", cl::desc("Output filename"), cl::value_desc("filename"));

static cl::opt<unsigned>
TimeCompilations("time-compilations", cl::Hidden, cl::init(1u),
                 cl::value_desc("N"),
                 cl::desc("Repeat compilation N times for timing"));

static cl::opt<bool>
NoIntegratedAssembler("no-integrated-as", cl::Hidden,
                      cl::desc("Disable integrated assembler"));

// Determine optimization level.
static cl::opt<char>
OptLevel("O",
         cl::desc("Optimization level. [-O0, -O1, -O2, or -O3] "
                  "(default = '-O2')"),
         cl::Prefix,
         cl::ZeroOrMore,
         cl::init(' '));

static cl::opt<std::string>
TargetTriple("mtriple", cl::desc("Override target triple for module"));

static cl::opt<bool> NoVerify("disable-verify", cl::Hidden,
                              cl::desc("Do not verify input module"));

static cl::opt<bool> DisableSimplifyLibCalls("disable-simplify-libcalls",
                                             cl::desc("Disable simplify-libcalls"));

static cl::opt<bool> ShowMCEncoding("show-mc-encoding", cl::Hidden,
                                    cl::desc("Show encoding in .s output"));

static cl::opt<bool> EnableDwarfDirectory(
    "enable-dwarf-directory", cl::Hidden,
    cl::desc("Use .file directives with an explicit directory."));

static cl::opt<bool> AsmVerbose("asm-verbose",
                                cl::desc("Add comments to directives."),
                                cl::init(true));




/*
enum {
  LOADI = 0, STOREI = 1, CONSTT = 2, ADDI = 3, COPYI = 4, ADDRLP = 5  
};

typedef struct tree {
  int op;
  int inst_num;
  struct tree *kids[2];
  int val;
  int num_kids;
  Instruction* inst;
  struct { struct burm_state *state; } x;
} *Tree;
*/


void updateSymTable(Instruction* inst) {
  int offset = getNexOff();
  //errs() << "instruction: " << *inst << " offset " << offset << "\n";
  SymTable.insert( std::make_pair(inst, offset) );
}


void printNodes() {
  errs() << "Total number of nodes : " << nodes.size() << "\n";
 
  for( auto it = nodes.begin(); it != nodes.end(); ++it ) {
    errs() << "Node " << (it->second)->inst_num  << " : \n" ;
    errs() << "Operation " << (it->second)->op <<"\n";
    errs() << "Instruction " << (it->second)->inst << "\n";
    
    int num_kids = (it->second)->num_kids;
    errs() << num_kids <<  " Kids : ";
    
    for(int i = 0; i< num_kids; i++)
      errs() << ((it->second)->kids[i])->inst_num <<" ";
    errs() << "\n";
  }
}


void printTrees(Tree t) {
  //std::string ret = std::to_string(t->op) + "( ";
  // errs() << ret << " " << t->num_kids << "\n";
  errs() << t->num_kids << "( ";
  
  for ( int i=0; i<t->num_kids; i++) {
    printTrees(t->kids[i]);
    errs() << " ";
  } 
  // errs() << ret << " " << t->num_kids << "\n";
  errs() << ") ";

}

void printRoots() {

  errs() << "Total number of expression trees : " << roots.size() << "\n";

  int count=0;
  for( auto it = roots.begin(); it != roots.end(); ++it) {
    count++;
    errs() << "Tree " << count <<"\n";
 
    printTrees(it->second);
    errs() << "\n";
    // std::queue<Tree> q;
    
    // q.push(it->second);
    
    // while( q.size() > 0 && count <20) {
    //   count++;
    //   Tree t = q.front();
    //   q.pop();
      
    //   int num_kids = t->num_kids;
    //   errs() << t->num_kids << " Kids :";
    //   for(int i = 0; i< num_kids; i++) {
    // 	errs() << t->kids[i]->inst_num << ", ";
    // 	q.push(t->kids[i]); 
    //   }
      
    // }
    // errs() << "\n\n";
  }
} 



Tree makeConstantNode(Instruction* inst, int idx) {
  Tree child = (Tree) malloc(sizeof *child);
  child->num_kids = 0;
  child->op = CNSTT;
  child->inst = inst;
  child->inst_num = idx;
  return child;
}


Tree makeCopyNode(Instruction* inst) {
  Tree child = (Tree) malloc(sizeof *child);
  child->num_kids = 0;
  child->op = COPYI; 
  child->inst = inst;
  child->inst_num = -1;
  return child;
}

Tree makeGlobalNode(Instruction* inst) {
  Tree child = (Tree) malloc(sizeof *child);
  child->num_kids = 0;
  child->op = GLOBI; 
  child->inst = inst;
  child->inst_num = -1;
  return child;
}

Tree makeAddressNode(Instruction* inst, int idx) {
  Tree child = (Tree) malloc(sizeof *child);
  child->num_kids = 0;
  Instruction *opinst;
  if (isa<GlobalValue>(inst->getOperand(idx)))
  {
    opinst = (Instruction *)(inst->getOperand(idx));
    child->op = GLOBI;
    child->inst = opinst;
    child->inst_num = -2;
    return child;
  }

  opinst = dyn_cast<Instruction>(inst->getOperand(idx));
  if(strcmp(opinst->getOpcodeName(), "alloca") == 0)
  {
    child->op = ADDRLP;
    child->inst = inst;
  }
  else 
  {
    child->op = LOADI;
    child->inst = opinst;
  }
  child->inst_num = idx;
  return child;
}

bool setTreeNode(Tree t, Instruction* inst) {
  

  switch(inst->getOpcode()) {
    
    // Load instruction - this will be a leaf node
  case Instruction::Load: {
    t->op = LOADI;
    t->inst = inst;
    t->num_kids = 0;
    break;
  }

    // Store instruction
  case Instruction::Store: {
    //errs() << "Instruction Store: ";
    t->op = STOREI;
    t->inst = inst; 
    t->num_kids = 2;

    Tree child0 = (Tree) malloc(sizeof *child0);
    Tree child1 = (Tree) malloc(sizeof *child1);

    Instruction* kidinst0 = dyn_cast<Instruction>(inst->getOperand(0));  
    //Instruction* kidinst1 = dyn_cast<Instruction>(inst->getOperand(1));
    //errs() << "Child 1 type " << *(inst->getOperand(1)->getType()) << "\n";
    // Computing the left child of store node
    if(isa<Constant>(inst->getOperand(0))) {
      free (child0);
      child0 = makeConstantNode(inst, 0);
    }

    else {      
    
      // If this operand is not in the symbol table, throw an error
      //if(SymTable.find(kidinst0) == SymTable.end()) {
    	//errs() << "Operand " << kidinst0 << "is undefined \n";
    	//return false;
      //}
    
      // If this operand is a root, we will create a copy node
      if(roots.find(kidinst0) != roots.end()) {
    	free (child0);
	child0 = makeCopyNode(kidinst0);
      }
      
      // If it not a root, we can simply locate it in nodes map
      // and make it the left child
      else if (nodes.find(kidinst0) != nodes.end()) {
	free (child0);
    	child0 = nodes[kidinst0];
      }
      
      // If it not in the nodes map, then we need to first load it
      else {
	free (child0);
	child0 = makeAddressNode(inst, 0);
      }   

         
    }


    // Computing the right child of store node
    // Note that this is a new node
    // This is because the IR is in SSA form
    // As a result, this variable has not been defined before  
    free (child1);
    child1 = makeAddressNode(inst, 1);

    // NOTE This part is a bit strange. The left child must be kids[1], and the right child is kids[0].
    // This is due to our grammar, which has the address on left and register on right.
    // However, in llvm, the address operand is the second operand, the register is the first.
    t->kids[1] = child0;  
    t->kids[0] = child1;

    // NOTE Do we need two children? Maybe we can do with only one.
    //  The address will then be an argument

    break;
  }

  case Instruction::Br: {
    
    if(dyn_cast<BranchInst>(inst)->isUnconditional()) {
      t->op = UJUMPI;
      t->inst = inst;
      t->num_kids = 0;
      labelTable.insert( std::make_pair(inst->getOperand(0), std::to_string(labelCount++)) );
      return true;
    }
    
    t->op = JUMPI;
    t->inst = inst;
    t->num_kids = 1;
    labelTable.insert( std::make_pair(inst->getOperand(1), std::to_string(labelCount++)) );
    labelTable.insert( std::make_pair(inst->getOperand(2), std::to_string(labelCount++)) );

    Instruction* operand = dyn_cast<Instruction>(inst->getOperand(0));

    if(isa<Constant>(inst->getOperand(0))) {
      t->kids[0] = makeConstantNode(inst, 0);
    }

    if(roots.find(operand) != roots.end()) {
      t->kids[0] = makeCopyNode(operand);
    }
      
    // If it not a root, we can simply locate it in nodes map
    // and make it the child
    else if (nodes.find(operand) != nodes.end()){
      t->kids[0] = nodes[operand];
    } 
    break;
  }

  case Instruction::ICmp: {

    t->op = ICMPI;
    
    t->inst = inst;
    t->num_kids = 2;
    
    
    for(int b=0; b < 2; b++ ) {
      Instruction* operand = dyn_cast<Instruction>(inst->getOperand(b));
      
      if(isa<Constant>(inst->getOperand(b))) {
	t->kids[b] = makeConstantNode(inst, b);
       
      }
      
      // NOTE Do we need to do any error checking?

      // else if(nodes.find(operand) == nodes.end()) {
      // 	errs() << "Operand " << operand << "is undefined \n";
      // 	return false;
      // }
      
      // If this operand is a root, we will create a copy node
      else if(roots.find(operand) != roots.end()) {
	errs() << "Reached ICMPI constant part\n";
	t->kids[b] = makeCopyNode(operand);
      }
      
      // If it not a root, we can simply locate it in nodes map
      // and make it the child
      else {
	t->kids[b] = nodes[operand];
      }

    }
    break;
  }

    // Binary operator instruction
  case Instruction::Add: 
  case Instruction::Sub: 
  case Instruction::Mul: 
  case Instruction::UDiv: 
  case Instruction::SDiv: 
  case Instruction::And: 
  case Instruction::Or: 
  case Instruction::Xor: 
  {
    t->op = ADDI1;
    t->inst = inst;
    t->num_kids = 2;
    
    // Next, we will generate nodes for children of this node
    for(int b = 0; b<2; ++b) {
      // We need to construct/locate the nodes corresponding to the child of this add node
      // First, check if it is a constant

      Instruction *kidinst = dyn_cast<Instruction>(inst->getOperand(b));
      if(isa<Constant>(inst->getOperand(b))) {
	t->kids[b] = makeConstantNode(inst, b);
      }
    
      // If it is not a constant, then it has been computed before this instruction
      // Therefore, it is either a root (in which case we will create a copy)
      // or a node in the nodes list (in which case we will make that the child of this node)
      else {
      
	// If this operand is not defined at this point, throw an error
	if(nodes.find(kidinst) == nodes.end()) {
	  errs() << "Operand " << kidinst << "is undefined \n";
	  return false;
	}
      
	// If this operand is a root, we will create a copy node
	if(roots.find(kidinst) != roots.end()) {
	  t->kids[b] = makeCopyNode(kidinst);
	}
      
	// If it not a root, we can simply locate it in nodes map
	// and make it the child
	else {
	  t->kids[b] = nodes[kidinst];
	}
      }
    }
    break;
  }
  default: errs() << "Instruction not supported\n";
    return false;
  }
  return true; 	
}


// main - Entry point for the llc compiler.

int main(int argc, char **argv) {
  sys::PrintStackTraceOnErrorSignal();
  PrettyStackTraceProgram X(argc, argv);

  // Enable debug stream buffering.
  EnableDebugBuffering = true;

  LLVMContext &Context = getGlobalContext();
  llvm_shutdown_obj Y;  // Call llvm_shutdown() on exit.

  // Initialize targets first, so that --version shows registered targets.
  InitializeAllTargets();
  InitializeAllTargetMCs();
  InitializeAllAsmPrinters();
  InitializeAllAsmParsers();

  // Initialize codegen and IR passes used by llc so that the -print-after,
  // -print-before, and -stop-after options work.
  PassRegistry *Registry = PassRegistry::getPassRegistry();
  initializeCore(*Registry);
  initializeCodeGen(*Registry);
  initializeLoopStrengthReducePass(*Registry);
  initializeLowerIntrinsicsPass(*Registry);
  initializeUnreachableBlockElimPass(*Registry);

  // Register the target printer for --version.
  cl::AddExtraVersionPrinter(TargetRegistry::printRegisteredTargetsForVersion);

  cl::ParseCommandLineOptions(argc, argv, "llvm system compiler\n");

  std::unique_ptr<Module> M;

  SMDiagnostic Err;
  
  M = parseIRFile(InputFilename, Err, Context);
  
  if (!M) {
    Err.print(argv[0], errs());
    return 1;
  }
  
  int count = 0;
  int regNum = 3;
  std::string RegArray[14] = {"%rax", "%rbx", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "%r9", "%8", "%rcx", "%rdx",
				"%rsi", "%rdi"};

  // Get the active pool of registers
  for (int i = 0; i < regNum; ++i)
    pools.insert(RegArray[i]);

  int num = 0;
  // First we iterate over all instructions in the module
  for(Module::iterator func_itr = M->begin(); func_itr != M->end(); ++func_itr) {
    for(Function::iterator BB_itr = func_itr->begin(); BB_itr != func_itr->end(); ++BB_itr) {
      for(BasicBlock::iterator inst_itr = BB_itr->begin(); inst_itr != BB_itr->end(); ++inst_itr) {


	// inst_itr points to an instruction in module M
	count ++;

        // Assign order to each instruction for calculation of life time interval
        InstIdx.insert( std::make_pair(inst_itr, count));

	errs() << "Instruction  " << count << ": " << *inst_itr << " has " << inst_itr->getNumOperands() << " operands : ";
	for(unsigned int i=0; i < inst_itr->getNumOperands(); i++) {
	  if(isa<Constant>(inst_itr->getOperand(i)))
	    errs() << dyn_cast<Constant>(inst_itr->getOperand(i))<<" ";
	  else 
	    errs() << dyn_cast<Instruction>(inst_itr->getOperand(i)) <<" ";

        /*  if(isa<GlobalValue>(inst_itr->getOperand(i))) {
            Instruction *inst = (Instruction *)inst_itr->getOperand(i);
            if (gvars.find(inst) == gvars.end())
            {
              Tree t = makeGlobalNode(inst);
              gvars.insert( std::make_pair(inst, t));
            }
            //errs() << "Instruction " << *inst << " global opcode name " << *(inst->getOperand(0)) << "\n";
          }*/
	}
	errs() << "\n";
	
	// Update symbol table --- not sure where this instruction should come
	// Update Global data
	if(strcmp(inst_itr->getOpcodeName(), "load") == 0 && isa<GlobalValue>(inst_itr->getOperand(0)))
        {
          Instruction *inst = (Instruction *) inst_itr->getOperand(0);
          gvec.push_back(inst);
        }

	// If instruction is an alloca, then we only need to update the symbol table. 
	if(strcmp(inst_itr->getOpcodeName(), "alloca") == 0)
        {
	  updateSymTable(inst_itr);
          continue;
	}


	if(strcmp(inst_itr->getOpcodeName(), "ret") == 0)
	  continue;
	
	if(strcmp(inst_itr->getOpcodeName(), "call") == 0)
	  continue;
	
	// Otherwise, we need to create node corresponding to this instruction
	Tree t = (Tree) malloc(sizeof *t);
	
	bool b = setTreeNode(t, inst_itr);
	
        // Calculate the lifetime interval 
	updateLifeInterval(t);


	t->inst_num = count;
	//errs() << t->kids[1]->op<< "inside main\n"; 

	// if(!setTreeNode(t, inst_itr)) 
	//   return 0;
	
	nodes.insert( std::make_pair(inst_itr, t) );

	// Finally, if inst_itr has multiple uses, we make it a root node
	if(inst_itr->getNumUses() >= 2) {  
	  roots.insert( std::make_pair(inst_itr, t) );
          rootKeys.push_back(t);
	}
	
	// If inst_itr is a store instruction, we make it a root node
	if(inst_itr->getOpcode() == Instruction::Store) {
	  roots.insert(std::make_pair(inst_itr, t) );
          rootKeys.push_back(t);
	}

	if(inst_itr->getOpcode() == Instruction::Br) {
	  roots.insert(std::make_pair(inst_itr, t) );
          rootKeys.push_back(t);
	}
      }
    }
  }
  
  for(Module::iterator func_itr = M->begin(); func_itr != M->end(); ++func_itr) 
  {
    for(Function::iterator BB_itr = func_itr->begin(); BB_itr != func_itr->end(); ++BB_itr) 
    {
      for(BasicBlock::iterator inst_itr = BB_itr->begin(); inst_itr != BB_itr->end(); ++inst_itr) 
      {
        if (nodes.find(inst_itr) == nodes.end())
          continue;
	errs() << "Instruction " << InstIdx[inst_itr] << ": " << *inst_itr <<" has life time interval " << nodes[inst_itr]->start << " to " << nodes[inst_itr]->end << "\n";
      }
    }
  }
  
  for( Tree t : rootKeys ) {
    gen(t);
    }
  
  GlobalLayOut();
  errs() << "Nodes corresponding to program instructions: \n"; 
  //printNodes();

  // errs() << "Trees corresponding to program instructions: \n";
  // printRoots();

  return 0;
}
