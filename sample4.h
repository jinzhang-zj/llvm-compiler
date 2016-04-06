#ifndef __OLIVE_HEADER_INCLUDED__
#define __OLIVE_HEADER_INCLUDED__
#include <assert.h>
#include <iostream>
#include <stdlib.h>
#include <string>
/*
   FILE: sample4.brg
  
   Copyright (c) 1997 Princeton University

   All rights reserved.

   This software is to be used for non-commercial purposes only,
   unless authorized permission to do otherwise is obtained.  
   For more information, contact spam@ee.princeton.edu
*/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unordered_set>
#include <sstream>
enum {
  LOADI=1, STOREI=2, CNSTT=3, BINOP1=4,
  BINOP2=5, STOREI2=10, GLOBI=51,
  COPYI=6, ADDRLP=7, ASGNI=8, MEM=9,
  ICMPI=111, JUMPI=112, UJUMPI=113, RETI=114,
  URET=115
};

typedef struct tree {
  int op;
  int inst_num;
  struct tree *kids[2];
  int val;
  int start;
  int end;
  std::string bb;
  int num_kids;
  Instruction *inst;      
  struct { struct burm_state *state; } x;
} *NODEPTR, *Tree;

#define GET_KIDS(p)	((p)->kids)
#define PANIC printf
#define STATE_LABEL(p) ((p)->x.state)
#define SET_STATE(p,s) (p)->x.state=(s)
#define DEFAULT_COST	break
#define NO_ACTION(x)

typedef struct COST {
    int cost;
} COST;
#define COST_LESS(a,b) ((a).cost < (b).cost)

static COST COST_INFINITY = { 32767 };
static COST COST_ZERO     = { 0 };

/*static char* burm_string = "FOO";*/
static int _ern = 0;

static int shouldTrace = 0;
static int shouldCover = 0;

int OP_LABEL(NODEPTR p) {
	switch (p->op) {
	//case CNSTT:  if (p->val == 0) return 661 /* I0I */;
	default:     return p->op;
	}
}

static void burm_trace(NODEPTR, int, COST);

std::vector<Tree> rootKeys;
std::unordered_set<std::string> pools;			// active pool of registers
std::map<Instruction*, Tree> roots;
std::map<Instruction*, Tree> nodes;
std::vector<Instruction*> gvec;
std::map<Instruction*, int> SymTable;	// Instruction and offset in stack
std::map<Instruction*, int> InstIdx;	// Instruction and its number
std::map<Instruction*, std::string> RegTable;  // Instruction and register
std::map<std::string, Instruction*> InsTable;  // Register and instruction
std::map<BasicBlock*, std::string> labelTable;  // Instruction and label
std::map<BasicBlock*, int> printed; // Keeps track of whether basic block label has been printed
int labelCount = 0;

int offCount = -8;	// Global value for offset count
static int getNexOff()
{
  offCount -= 8;
  return offCount + 8;
}

// Expire the old register that's not useful
static void expireOldInterval(Instruction *inst) {
  int T = InstIdx[inst];
  for (auto it = InsTable.begin(); it != InsTable.end(); ++it)
  {
    NODEPTR cur = nodes[it->second];
    if (cur->end <= T)
    {
      pools.insert(it->first);
      InsTable.erase(it->first);
      RegTable.erase(it->second);
    }
  }
}

static std::string spillAtInterval(Instruction *inst)
{
  int maxEnd = -1;
  Instruction *maxIns = NULL;

  for (auto it = InsTable.begin(); it != InsTable.end(); ++it)
  {
    NODEPTR cur = nodes[it->second];
    if (cur->end > maxEnd && inst != it->second)
    {
      maxEnd = cur->end;
      maxIns = cur->inst;
    }
  }

  std::string reg = RegTable[maxIns];
  int offset = getNexOff();
  RegTable[maxIns] = std::to_string(offset) + "(%rbp)";
  InsTable.erase(reg);
  std::cout << "\tmovq\t" << reg << ", " << RegTable[maxIns] << "\n";
  return reg;
}

void spillReg(std::string reg)
{
  if (InsTable.find(reg) == InsTable.end())
    return;
  Instruction *inst = InsTable[reg];
  int offset = getNexOff();
  RegTable[inst] = std::to_string(offset) + "(%rbp)";
  InsTable.erase(reg);
  std::cout << "\tmovq\t" << reg << ", " << RegTable[inst] << "\n";
}

// Allocate register with linear scan algorithm
static std::string getNexReg(Instruction *inst) {
  // expire old register first
  expireOldInterval(inst);

  // Get a new one with linear scan algorithm
  std::string reg;
  if (!pools.empty())
  {
    auto it = pools.begin();
    reg = *it;
    pools.erase(reg);
  }
  else
  {
    // spill
    reg = spillAtInterval(inst);
  }

  return reg;
}

std::string binop(Instruction *inst)
{
  switch (inst->getOpcode()) {
    case Instruction::Add : return "\taddq\t";
    case Instruction::Sub : return "\tsubq\t";
    case Instruction::Mul : return "\timulq\t";
    case Instruction::UDiv : return "\tdivq\t";
    case Instruction::SDiv : return "\tidivq\t";
    case Instruction::Shl : return "\tsalq\t";
    case Instruction::LShr : return "\tshrq\t";
    case Instruction::AShr : return "\tsarq\t";
    case Instruction::And : return "\tandq\t";
    case Instruction::Or :  return "\torq\t";
    case Instruction::Xor :  return "\txorq\t";
    default: return "\tunknown\t";
  }
}

#define BURP 0
#define LOADI 1
#define STOREI 2
#define CNSTT 3
#define BINOP1 4
#define BINOP2 5
#define COPYI 6
#define ADDRLP 7
#define ASGNI 8
#define MEM 9
#define STOREI2 10
#define ICMPI 11
#define JUMPI 12
#define UJUMPI 13
#define GLOBI 14
#define RETI 15
#define URET 16

struct burm_state {
  int op;
  NODEPTR node;
  struct burm_state **kids;
  COST cost[7];
  struct {
    unsigned burm_stmt:4;
    unsigned burm_reg:3;
    unsigned burm_disp:3;
    unsigned burm_rc:2;
    unsigned burm_con:1;
    unsigned burm__:1;
  } rule;
};


struct burm_state *burm_label(NODEPTR);
struct burm_state *burm_label1(NODEPTR);

void dumpCover(NODEPTR,int,int);

#define burm_stmt_NT 1
#define burm_reg_NT 2
#define burm_disp_NT 3
#define burm_rc_NT 4
#define burm_con_NT 5
#define burm___NT 6
extern int burm_max_nt;


std::string stmt_action(struct burm_state *_s, 

int indent);


std::string reg_action(struct burm_state *_s, 

int indent);


std::string disp_action(struct burm_state *_s, 

int indent);


std::string rc_action(struct burm_state *_s, 

int indent);


std::string con_action(struct burm_state *_s, 

int indent);
#ifndef ALLOC
#define ALLOC(n) malloc(n)
#endif

#ifndef burm_assert
#define burm_assert(x,y) if (!(x)) {  y; abort(); }
#endif

static NODEPTR burm_np;

#define burm_stmt_NT 1
#define burm_reg_NT 2
#define burm_disp_NT 3
#define burm_rc_NT 4
#define burm_con_NT 5
#define burm___NT 6
extern int burm_max_nt;
int burm_max_nt = 6;

std::string burm_ntname[] = {
  "",
  "stmt",
  "reg",
  "disp",
  "rc",
  "con",
  "_",
  ""
};

static short burm_nts_0[] = { burm___NT, burm___NT, burm___NT, 0 };
static short burm_nts_1[] = { 0 };
static short burm_nts_2[] = { burm_disp_NT, burm_rc_NT, 0 };
static short burm_nts_3[] = { burm_reg_NT, burm_rc_NT, 0 };
static short burm_nts_4[] = { burm_disp_NT, burm_disp_NT, 0 };
static short burm_nts_5[] = { burm_rc_NT, 0 };
static short burm_nts_6[] = { burm_reg_NT, 0 };
static short burm_nts_7[] = { burm_con_NT, burm_con_NT, 0 };
static short burm_nts_8[] = { burm_rc_NT, burm_reg_NT, 0 };
static short burm_nts_9[] = { burm_con_NT, 0 };

short *burm_nts[] = {
  burm_nts_0,  /* 0 */
  burm_nts_1,  /* 1 */
  burm_nts_2,  /* 2 */
  burm_nts_3,  /* 3 */
  burm_nts_3,  /* 4 */
  burm_nts_4,  /* 5 */
  burm_nts_1,  /* 6 */
  burm_nts_5,  /* 7 */
  burm_nts_6,  /* 8 */
  burm_nts_6,  /* 9 */
  burm_nts_1,  /* 10 */
  burm_nts_7,  /* 11 */
  burm_nts_3,  /* 12 */
  burm_nts_8,  /* 13 */
  burm_nts_1,  /* 14 */
  burm_nts_1,  /* 15 */
  burm_nts_7,  /* 16 */
  burm_nts_3,  /* 17 */
  burm_nts_8,  /* 18 */
  burm_nts_1,  /* 19 */
  burm_nts_9,  /* 20 */
  burm_nts_6,  /* 21 */
  burm_nts_1,  /* 22 */
};

char burm_arity[] = {
  3,  /* 0=BURP */
  0,  /* 1=LOADI */
  2,  /* 2=STOREI */
  0,  /* 3=CNSTT */
  2,  /* 4=BINOP1 */
  2,  /* 5=BINOP2 */
  0,  /* 6=COPYI */
  0,  /* 7=ADDRLP */
  0,  /* 8=ASGNI */
  0,  /* 9=MEM */
  2,  /* 10=STOREI2 */
  2,  /* 11=ICMPI */
  1,  /* 12=JUMPI */
  0,  /* 13=UJUMPI */
  0,  /* 14=GLOBI */
  1,  /* 15=RETI */
  0,  /* 16=URET */
};

std::string burm_opname[] = {
  /* 0 */  "BURP",
  /* 1 */  "LOADI",
  /* 2 */  "STOREI",
  /* 3 */  "CNSTT",
  /* 4 */  "BINOP1",
  /* 5 */  "BINOP2",
  /* 6 */  "COPYI",
  /* 7 */  "ADDRLP",
  /* 8 */  "ASGNI",
  /* 9 */  "MEM",
  /* 10 */  "STOREI2",
  /* 11 */  "ICMPI",
  /* 12 */  "JUMPI",
  /* 13 */  "UJUMPI",
  /* 14 */  "GLOBI",
  /* 15 */  "RETI",
  /* 16 */  "URET",
};


std::string burm_string[] = {
  /* 0 */  "stmt: BURP(_,_,_)",
  /* 1 */  "stmt: URET",
  /* 2 */  "stmt: STOREI(disp,rc)",
  /* 3 */  "reg: ICMPI(reg,rc)",
  /* 4 */  "stmt: STOREI(reg,rc)",
  /* 5 */  "stmt: STOREI2(disp,disp)",
  /* 6 */  "stmt: UJUMPI",
  /* 7 */  "stmt: JUMPI(rc)",
  /* 8 */  "stmt: reg",
  /* 9 */  "stmt: RETI(reg)",
  /* 10 */  "reg: COPYI",
  /* 11 */  "reg: BINOP1(con,con)",
  /* 12 */  "reg: BINOP1(reg,rc)",
  /* 13 */  "reg: BINOP2(rc,reg)",
  /* 14 */  "reg: LOADI",
  /* 15 */  "disp: ADDRLP",
  /* 16 */  "disp: BINOP1(con,con)",
  /* 17 */  "disp: BINOP1(reg,rc)",
  /* 18 */  "disp: BINOP2(rc,reg)",
  /* 19 */  "disp: GLOBI",
  /* 20 */  "rc: con",
  /* 21 */  "rc: reg",
  /* 22 */  "con: CNSTT",
};


std::string burm_files[] = {
"sample4.brg",
};

int burm_file_numbers[] = {
  /* 0 */  0,
  /* 1 */  0,
  /* 2 */  0,
  /* 3 */  0,
  /* 4 */  0,
  /* 5 */  0,
  /* 6 */  0,
  /* 7 */  0,
  /* 8 */  0,
  /* 9 */  0,
  /* 10 */  0,
  /* 11 */  0,
  /* 12 */  0,
  /* 13 */  0,
  /* 14 */  0,
  /* 15 */  0,
  /* 16 */  0,
  /* 17 */  0,
  /* 18 */  0,
  /* 19 */  0,
  /* 20 */  0,
  /* 21 */  0,
  /* 22 */  0,
};

int burm_line_numbers[] = {
  /* 0 */  194,
  /* 1 */  202,
  /* 2 */  215,
  /* 3 */  227,
  /* 4 */  244,
  /* 5 */  255,
  /* 6 */  273,
  /* 7 */  285,
  /* 8 */  330,
  /* 9 */  341,
  /* 10 */  355,
  /* 11 */  377,
  /* 12 */  397,
  /* 13 */  428,
  /* 14 */  459,
  /* 15 */  500,
  /* 16 */  524,
  /* 17 */  544,
  /* 18 */  576,
  /* 19 */  608,
  /* 20 */  625,
  /* 21 */  635,
  /* 22 */  645,
};

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-variable"

static short burm_decode_stmt[] = {
   -1,
  0,
  1,
  2,
  4,
  5,
  6,
  7,
  8,
  9,
};

static short burm_decode_reg[] = {
   -1,
  3,
  10,
  11,
  12,
  13,
  14,
};

static short burm_decode_disp[] = {
   -1,
  15,
  16,
  17,
  18,
  19,
};

static short burm_decode_rc[] = {
   -1,
  20,
  21,
};

static short burm_decode_con[] = {
   -1,
  22,
};

static short burm_decode__[] = {
   -1,
};

int burm_rule(struct burm_state *state, int goalnt) {
  burm_assert(goalnt >= 1 && goalnt <= 6,
        PANIC("Bad goal nonterminal %d in burm_rule\n", goalnt));
  if (!state)
    return 0;
  switch (goalnt) {
  case burm_stmt_NT:  return burm_decode_stmt[((struct burm_state *)state)->rule.burm_stmt];
  case burm_reg_NT:  return burm_decode_reg[((struct burm_state *)state)->rule.burm_reg];
  case burm_disp_NT:  return burm_decode_disp[((struct burm_state *)state)->rule.burm_disp];
  case burm_rc_NT:  return burm_decode_rc[((struct burm_state *)state)->rule.burm_rc];
  case burm_con_NT:  return burm_decode_con[((struct burm_state *)state)->rule.burm_con];
  case burm___NT:  return burm_decode__[((struct burm_state *)state)->rule.burm__];
  default:
    burm_assert(0, PANIC("Bad goal nonterminal %d in burm_rule\n", goalnt));
  }
  return 0;
}


struct burm_action {
  int nt;
  struct burm_state* st;
};

#ifndef RULE
#define RULE(n,s) \
    (act = (burm_action*) malloc(sizeof(struct burm_action)),act->nt=n,act->st=s,act)
#endif

int burm_cost_code(COST *_c, int _ern,struct burm_state *_s)
{
  NODEPTR *_children;
  struct burm_action *act;
  switch(_ern){
  default:
    DEFAULT_COST;
  case 0:
    _children = GET_KIDS(_s->node);
{


 return 1; 
}
  break;
  case 1:
{


 (*_c).cost=0;
}
  break;
  case 2:
{


 (*_c).cost=_s->kids[0]->cost[burm_disp_NT].cost+_s->kids[1]->cost[burm_rc_NT].cost+1; 
}
  break;
  case 3:
{


 (*_c).cost=_s->kids[0]->cost[burm_reg_NT].cost+_s->kids[1]->cost[burm_rc_NT].cost+1; 
}
  break;
  case 4:
{


 (*_c).cost=_s->kids[0]->cost[burm_reg_NT].cost+_s->kids[1]->cost[burm_rc_NT].cost+1; 
}
  break;
  case 5:
{


 (*_c).cost=_s->kids[0]->cost[burm_disp_NT].cost+_s->kids[1]->cost[burm_disp_NT].cost+1; 
}
  break;
  case 6:
{


 (*_c).cost=1;
}
  break;
  case 7:
{


 (*_c).cost=_s->kids[0]->cost[burm_rc_NT].cost+1;
}
  break;
  case 8:
{


 (*_c).cost=_s->cost[burm_reg_NT].cost; 
}
  break;
  case 9:
{


 (*_c).cost=_s->kids[0]->cost[burm_reg_NT].cost + 1; 
}
  break;
  case 10:
{


 (*_c).cost=1; 
}
  break;
  case 11:
{


 (*_c).cost=_s->kids[0]->cost[burm_con_NT].cost+_s->kids[1]->cost[burm_con_NT].cost+1; 
}
  break;
  case 12:
{


 (*_c).cost=_s->kids[0]->cost[burm_reg_NT].cost+_s->kids[1]->cost[burm_rc_NT].cost+1; 
}
  break;
  case 13:
{


 (*_c).cost=_s->kids[0]->cost[burm_rc_NT].cost+_s->kids[1]->cost[burm_reg_NT].cost+1; 
}
  break;
  case 14:
{


 (*_c).cost=1; 
}
  break;
  case 15:
{


 (*_c).cost=0; 
}
  break;
  case 16:
{


 (*_c).cost=_s->kids[0]->cost[burm_con_NT].cost+_s->kids[1]->cost[burm_con_NT].cost+1; 
}
  break;
  case 17:
{


 (*_c).cost=_s->kids[0]->cost[burm_reg_NT].cost+_s->kids[1]->cost[burm_rc_NT].cost+1; 
}
  break;
  case 18:
{


 (*_c).cost=_s->kids[0]->cost[burm_rc_NT].cost+_s->kids[1]->cost[burm_reg_NT].cost+1; 
}
  break;
  case 19:
{


 (*_c).cost=0; 
}
  break;
  case 20:
{


 (*_c).cost=_s->cost[burm_con_NT].cost; 
}
  break;
  case 21:
{


 (*_c).cost=_s->cost[burm_reg_NT].cost; 
}
  break;
  case 22:
{


 (*_c).cost=0; 
}
  break;
  }
  return 1;
}


std::string stmt_action(struct burm_state *_s, 

int indent);


std::string reg_action(struct burm_state *_s, 

int indent);


std::string disp_action(struct burm_state *_s, 

int indent);


std::string rc_action(struct burm_state *_s, 

int indent);


std::string con_action(struct burm_state *_s, 

int indent);


#include <stdarg.h>

void burm_exec(struct burm_state *state, int nterm, ...) 
{
  va_list(ap);
  va_start(ap,nterm);

  burm_assert(nterm >= 1 && nterm <= 6,
        PANIC("Bad nonterminal %d in $exec\n", nterm));

  if (state)
    switch (nterm) {
    case burm_stmt_NT:
      PANIC("$exec cannot take non-void functions as arguments\n");
      break;
    case burm_reg_NT:
      PANIC("$exec cannot take non-void functions as arguments\n");
      break;
    case burm_disp_NT:
      PANIC("$exec cannot take non-void functions as arguments\n");
      break;
    case burm_rc_NT:
      PANIC("$exec cannot take non-void functions as arguments\n");
      break;
    case burm_con_NT:
      PANIC("$exec cannot take non-void functions as arguments\n");
      break;
    default:
      PANIC("Bad nonterminal %d in $exec\n", nterm);
      break;
    }
  else
    PANIC("Bad state for $exec in nonterminal %d \n",nterm);
  va_end(ap);
}

#define EXEC(s,n,a) ( \
  PANIC("Bad nonterminal %d in $exec\n", n))

struct burm_state *burm_immed(struct burm_state *s,int n);
#ifndef NO_ACTION
#define NO_ACTION assert(0)
#endif


std::string stmt_action(struct burm_state *_s, 

int indent)
{
  struct burm_state *_t;
  int _ern=burm_decode_stmt[_s->rule.burm_stmt];
  NODEPTR *_children;
  if(_s->rule.burm_stmt==0)
    NO_ACTION(stmt);
  switch(_ern){
  case 0:
    _children = GET_KIDS(_s->node);
{



		stmt_action(burm_immed(_s,0),10);
                return "";
	
}
  break;
  case 1:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
		std::cout << "\tretq\t\n"; 
                return "";

	
}
  break;
  case 2:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
		std::cout << "\tmovq\t" + rc_action(_s->kids[1],indent+1) + ", " + disp_action(_s->kids[0],indent+1) + "\n";
		return "";
	
}
  break;
  case 4:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
		std::cout << "\tmovq\t" + rc_action(_s->kids[1],indent+1) + ", (" + reg_action(_s->kids[0],indent+1) + ")\n";
		return "";
	
}
  break;
  case 5:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
                std::string reg1 = getNexReg(_s->node->inst);
		RegTable[_s->node->inst] = reg1;
                InsTable[reg1] = _s->node->inst;
                std::cout << "\tleaq\t" << disp_action(_s->kids[1],indent+1) << ", " << reg1 << "\n";
		std::cout << "\tmovq\t" + reg1 + ", " + disp_action(_s->kids[0],indent+1) + "\n";
                pools.insert(reg1);
		return "";
	
}
  break;
  case 6:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
		NODEPTR cur = _s->node;
		std::cout << "\tjmp " + labelTable[dyn_cast<BasicBlock>(cur->inst->getOperand(0))] + "\n"; 
                return "";
	
}
  break;
  case 7:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
                std::string reg1 = rc_action(_s->kids[0],indent+1);
		
                NODEPTR cur = _s->node;
		NODEPTR child = cur->kids[0];
		int opr= (dyn_cast<CmpInst>(child->inst))->getPredicate();
		
		std::string x86opr = "";

                if (opr == 32)
                        x86opr = "\tje\t";
                else if (opr == 33)
                        x86opr = "\tjne\t";
                else if (opr == 34)
                        x86opr = "\tja\t";
               	else if (opr == 35)
                        x86opr = "\tjae\t";
                else if (opr == 36)
                        x86opr = "\jb\t";
                else if (opr == 37)
                        x86opr = "\tjbe\t";
                else if (opr == 38)
                        x86opr = "\tjg\t";
                else if (opr == 39)
                        x86opr = "\tjge\t";
                else if (opr == 40)
                        x86opr = "\tjl\t";
                else if (opr == 41)
                        x86opr = "\tjle\t";

		std::cout << x86opr + labelTable[dyn_cast<BasicBlock>(cur->inst->getOperand(1))] + "\n";
		std::cout << "\tjmp " + labelTable[dyn_cast<BasicBlock>(cur->inst->getOperand(2))] + "\n"; 
                return "";

	
}
  break;
  case 8:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
		return reg_action(_s,indent+1);
	
}
  break;
  case 9:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
                std::string reg1 = reg_action(_s->kids[0],indent+1);
                if (reg1.compare("%rax") != 0)
                  std::cout << "\tmovq\t" + reg1 + ", %rax\n";
		return "";
	
}
  break;
  }
}


std::string reg_action(struct burm_state *_s, 

int indent)
{
  struct burm_state *_t;
  int _ern=burm_decode_reg[_s->rule.burm_reg];
  NODEPTR *_children;
  if(_s->rule.burm_reg==0)
    NO_ACTION(reg);
  switch(_ern){
  case 3:
{



		int i;
                NODEPTR cur = _s->node;

		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
                std::string reg1 = reg_action(_s->kids[0],indent+1);
                std::cout << "\tcmp\t" + reg1 +  ", " + rc_action(_s->kids[1],indent+1) + "\n";
                RegTable[cur->inst] = reg1;
                return reg1;
	
}
  break;
  case 10:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
                std::string reg1 = getNexReg(_s->node->inst);
                if (reg1.compare(RegTable[_s->node->inst]) != 0)
                  std::cout << "\tmovq\t" + RegTable[_s->node->inst] + ", " + reg1 + "\n";
                if (RegTable[_s->node->inst][0] != '%')
                {
                  RegTable[_s->node->inst] = reg1;
                  InsTable[reg1] = _s->node->inst;
                }
                return reg1;
	
}
  break;
  case 11:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";

                NODEPTR cur = _s->node;
                Constant* cnst1 = dyn_cast<Constant>(cur->inst->getOperand(0));
                long long val1 = cnst1->getUniqueInteger().getSExtValue();
                Constant* cnst2 = dyn_cast<Constant>(cur->inst->getOperand(1));
                long long val2 = cnst2->getUniqueInteger().getSExtValue();
		std::string reg1 = getNexReg(cur->inst);
		std::cout << "\tmovq\t$" << std::to_string(val1 + val2) << ", " << reg1 << "\n";
		InsTable[reg1] = cur->inst;
		RegTable[cur->inst] = reg1;
		return reg1;
	
}
  break;
  case 12:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
                NODEPTR cur = _s->node;
                std::string reg1 = reg_action(_s->kids[0],indent+1);
                if (cur->inst->getOpcode() != Instruction::UDiv && 
                    cur->inst->getOpcode() != Instruction::SDiv)
                {
                  std::cout << binop(cur->inst) + rc_action(_s->kids[1],indent+1) + ", " + reg1 + "\n";
                  RegTable[cur->inst] = reg1;
                  InsTable[reg1] = cur->inst;
                  return reg1;
                }
                else if (reg1.compare("%rax") != 0)
                {
                  spillReg("%rdx");
                  spillReg("%rax");
                  std::cout << "\tmovq\t" << reg1 << ", %rax\n";
                  reg1 = "%rax";
                }
		std::cout << "\tcqto\n";
                std::cout << binop(cur->inst) + rc_action(_s->kids[1],indent+1) + "\n";
                RegTable[cur->inst] = reg1;
                InsTable[reg1] = cur->inst;
                return reg1;
	
}
  break;
  case 13:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
                std::string reg1 = reg_action(_s->kids[1],indent+1);
                NODEPTR cur = _s->node;
                if (cur->inst->getOpcode() != Instruction::UDiv && 
                    cur->inst->getOpcode() != Instruction::SDiv)
                {
                  std::cout << binop(cur->inst) + rc_action(_s->kids[0],indent+1) + ", " + reg1 + "\n";
                  RegTable[cur->inst] = reg1;
                  InsTable[reg1] = cur->inst;
                  return reg1;
                }
                else if (reg1.compare("%rax") != 0)
                {
                  spillReg("%rdx");
                  spillReg("%rax");
                  std::cout << "\tmovq\t" << reg1 << ", %rax\n";
                  reg1 = "%rax";
                }
		std::cout << "\tcqto\n";
                std::cout << binop(cur->inst) + rc_action(_s->kids[0],indent+1) + "\n";
                RegTable[cur->inst] = reg1;
                InsTable[reg1] = cur->inst;
                return reg1;
	
}
  break;
  case 14:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
                std::string reg1 = getNexReg(_s->node->inst);
		RegTable[_s->node->inst] = reg1;
                InsTable[reg1] = _s->node->inst;
                NODEPTR cur = _s->node;
                if (isa<GlobalValue>(cur->inst->getOperand(0)))
                {
		  Instruction *inst = (Instruction *) (cur->inst->getOperand(0));
		  std::string str;
		  llvm::raw_string_ostream rso(str);
		  inst->print(rso);
		  rso.flush();
    		  int idx = str.find_first_of(' ');
		  std::cout << "\tmovq\t" + str.substr(1, idx -1) + "(%rip), " + reg1 + "\n";
		  return reg1;
                }

                Instruction *inst = dyn_cast<Instruction>(cur->inst->getOperand(0));
                if (strcmp(inst->getOpcodeName(), "alloca") == 0)
                {
                  int offset = SymTable[inst];
                  std::cout << "\tmovq\t" + std::to_string(offset) + "(%rbp), " + reg1 + "\n";
                }
                else if (strcmp(inst->getOpcodeName(), "load") == 0)
                {
                  Instruction *kidinst = dyn_cast<Instruction>(inst->getOperand(0));
                  std::string reg2 = getNexReg(kidinst);
                  int offset = SymTable[kidinst];
                  std::cout << "\tmovq\t" + std::to_string(offset) + "(%rbp), " + reg2 + "\n";
                  std::cout << "\tmovq\t(" + reg2 + "), " + reg1 + "\n";
		  pools.insert(reg2);
                }
                return reg1;
	
}
  break;
  }
}


std::string disp_action(struct burm_state *_s, 

int indent)
{
  struct burm_state *_t;
  int _ern=burm_decode_disp[_s->rule.burm_disp];
  NODEPTR *_children;
  if(_s->rule.burm_disp==0)
    NO_ACTION(disp);
  switch(_ern){
  case 15:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
                NODEPTR cur = _s->node;
                Instruction *inst = dyn_cast<Instruction>(cur->inst->getOperand(cur->inst_num));
                Type *tp = cur->inst->getOperand(cur->inst_num)->getType();
                std::string tmpStr;
                llvm::raw_string_ostream rso(tmpStr);
                tp->print(rso);
                rso.flush();
                int level = 0;
                for (char c : tmpStr)
                  if (c == '*')
                    level++;
                int offset = 0;
                offset = SymTable[inst];
                std::string ret =  std::to_string(offset) + "(%rbp)";
                return ret;
	
}
  break;
  case 16:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";

                NODEPTR cur = _s->node;
                Constant* cnst1 = dyn_cast<Constant>(cur->inst->getOperand(0));
                long long val1 = cnst1->getUniqueInteger().getSExtValue();
                Constant* cnst2 = dyn_cast<Constant>(cur->inst->getOperand(1));
                long long val2 = cnst2->getUniqueInteger().getSExtValue();
		std::string reg1 = getNexReg(cur->inst);
		std::cout << "\tmovq\t$" << std::to_string(val1 + val2) << ", " << reg1 << "\n";
		InsTable[reg1] = cur->inst;
		RegTable[cur->inst] = reg1;
		return reg1;
	
}
  break;
  case 17:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";

                NODEPTR cur = _s->node;
                std::string reg1 = reg_action(_s->kids[0],indent+1);
                if (cur->inst->getOpcode() != Instruction::UDiv && 
                    cur->inst->getOpcode() != Instruction::SDiv)
                {
                  std::cout << binop(cur->inst) + rc_action(_s->kids[1],indent+1) + ", " + reg1 + "\n";
                  RegTable[cur->inst] = reg1;
                  InsTable[reg1] = cur->inst;
                  return reg1;
                }
                else if (reg1.compare("%rax") != 0)
                {
                  spillReg("%rdx");
                  spillReg("%rax");
                  std::cout << "\tmovq\t" << reg1 << ", %rax\n";
                  reg1 = "%rax";
                }
		std::cout << "\tcqto\n";
                std::cout << binop(cur->inst) + rc_action(_s->kids[1],indent+1) + "\n";
                RegTable[cur->inst] = reg1;
                InsTable[reg1] = cur->inst;
                return reg1;
	
}
  break;
  case 18:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
                std::string reg1 = reg_action(_s->kids[1],indent+1);
                NODEPTR cur = _s->node;
                if (cur->inst->getOpcode() != Instruction::UDiv && 
                    cur->inst->getOpcode() != Instruction::SDiv)
                {
                  std::cout << binop(cur->inst) + rc_action(_s->kids[0],indent+1) + ", " + reg1 + "\n";
                  RegTable[cur->inst] = reg1;
                  InsTable[reg1] = cur->inst;
                  return reg1;
                }
                else if (reg1.compare("%rax") != 0)
                {
                  spillReg("%rdx");
                  spillReg("%rax");
                  std::cout << "\tmovq\t" << reg1 << ", %rax\n";
                  reg1 = "%rax";
                }
		std::cout << "\tcqto\n";
                std::cout << binop(cur->inst) + rc_action(_s->kids[0],indent+1) + "\n";
                RegTable[cur->inst] = reg1;
                InsTable[reg1] = cur->inst;
                return reg1;
	
}
  break;
  case 19:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
		std::string str;
		llvm::raw_string_ostream rso(str);
		_s->node->inst->print(rso);
		rso.flush();
                int idx = str.find_first_of(' ');
		std::string rip = "(%rip)";
		return str.substr(1, idx - 1) + rip;
	
}
  break;
  }
}


std::string rc_action(struct burm_state *_s, 

int indent)
{
  struct burm_state *_t;
  int _ern=burm_decode_rc[_s->rule.burm_rc];
  NODEPTR *_children;
  if(_s->rule.burm_rc==0)
    NO_ACTION(rc);
  switch(_ern){
  case 20:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
		return con_action(_s,indent+1);
	
}
  break;
  case 21:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
		return reg_action(_s,indent+1);
	
}
  break;
  }
}


std::string con_action(struct burm_state *_s, 

int indent)
{
  struct burm_state *_t;
  int _ern=burm_decode_con[_s->rule.burm_con];
  NODEPTR *_children;
  if(_s->rule.burm_con==0)
    NO_ACTION(con);
  switch(_ern){
  case 22:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
                NODEPTR cur = _s->node;
                Constant* cnst = dyn_cast<Constant>(cur->inst->getOperand(cur->inst_num));
                int val = cnst->getUniqueInteger().getSExtValue();
                return "$" + std::to_string(val);
	
}
  break;
  }
}
static void burm_closure_reg(struct burm_state *, COST);
static void burm_closure_con(struct burm_state *, COST);

static void burm_closure_reg(struct burm_state *s, COST c) {
  if(burm_cost_code(&c,21,s) && COST_LESS(c,s->cost[burm_rc_NT])) {
burm_trace(burm_np, 21, c);     s->cost[burm_rc_NT] = c ;
    s->rule.burm_rc = 2;
  }
  if(burm_cost_code(&c,8,s) && COST_LESS(c,s->cost[burm_stmt_NT])) {
burm_trace(burm_np, 8, c);     s->cost[burm_stmt_NT] = c ;
    s->rule.burm_stmt = 8;
  }
}

static void burm_closure_con(struct burm_state *s, COST c) {
  if(burm_cost_code(&c,20,s) && COST_LESS(c,s->cost[burm_rc_NT])) {
burm_trace(burm_np, 20, c);     s->cost[burm_rc_NT] = c ;
    s->rule.burm_rc = 1;
  }
}

struct burm_state *burm_alloc_state(NODEPTR u,int op,int arity)
{
  struct burm_state *p, **k;
  p = (struct burm_state *)ALLOC(sizeof *p);
  burm_assert(p, PANIC("1:ALLOC returned NULL in burm_alloc_state\n"));
    burm_np = u;
  p->op = op;
  p->node = u;
  if(arity){
    k=(struct burm_state **)ALLOC(arity*sizeof (struct burm_state *));
    burm_assert(k, PANIC("2:ALLOC returned NULL in burm_alloc_state\n"));
    p->kids=k;
  }else
    p->kids=0;
  p->rule.burm_stmt =
  p->rule.burm_reg =
  p->rule.burm_disp =
  p->rule.burm_rc =
  p->rule.burm_con =
  p->rule.burm__ =
    0;
  p->cost[1] =
  p->cost[2] =
  p->cost[3] =
  p->cost[4] =
  p->cost[5] =
  p->cost[6] =
    COST_INFINITY;
  return p;
}
struct burm_state *burm_label1(NODEPTR u) {
  int op, arity, i, immed_matched=0;
  COST c=COST_ZERO;
  struct burm_state *s,**k;
  NODEPTR *children;
  op=OP_LABEL(u);
  arity=burm_arity[op];
  switch(op){
  case 0:		/* BURP */
    s=burm_alloc_state(u,op,arity);
    SET_STATE(u,s);
    k=s->kids;
        /*immediate rule: stmt: BURP(_,_,_) */
    if(burm_cost_code(&c,0,s) && COST_LESS(c,s->cost[burm_stmt_NT])) {
burm_trace(burm_np, 0, c);       s->cost[burm_stmt_NT] = c ;
      s->rule.burm_stmt = 1;
      immed_matched=1;
    }
    if(immed_matched){
      for(i=0;i<arity;i++)k[i]=0;
      return s;
    }
    break;
  case 1:		/* LOADI */
#ifdef LEAF_TRAP
    if(s=LEAF_TRAP(u,op))
      return s;
#endif
    s=burm_alloc_state(u,op,arity);
    SET_STATE(u,s);
    k=0;
    {  		/* reg: LOADI */
      if(burm_cost_code(&c,14,s) && COST_LESS(c,s->cost[burm_reg_NT])) {
burm_trace(burm_np, 14, c);         s->cost[burm_reg_NT] = c ;
        s->rule.burm_reg = 6;
        burm_closure_reg(s, c );
      }
    }
    break;
  case 2:		/* STOREI */
    s=burm_alloc_state(u,op,arity);
    SET_STATE(u,s);
    k=s->kids;
    children=GET_KIDS(u);
    for(i=0;i<arity;i++)
      k[i]=burm_label1(children[i]);
    if (   /* stmt: STOREI(reg,rc) */
      k[0]->rule.burm_reg && 
      k[1]->rule.burm_rc
    ) {
      if(burm_cost_code(&c,4,s) && COST_LESS(c,s->cost[burm_stmt_NT])) {
burm_trace(burm_np, 4, c);         s->cost[burm_stmt_NT] = c ;
        s->rule.burm_stmt = 4;
      }
    }
    if (   /* stmt: STOREI(disp,rc) */
      k[0]->rule.burm_disp && 
      k[1]->rule.burm_rc
    ) {
      if(burm_cost_code(&c,2,s) && COST_LESS(c,s->cost[burm_stmt_NT])) {
burm_trace(burm_np, 2, c);         s->cost[burm_stmt_NT] = c ;
        s->rule.burm_stmt = 3;
      }
    }
    break;
  case 3:		/* CNSTT */
#ifdef LEAF_TRAP
    if(s=LEAF_TRAP(u,op))
      return s;
#endif
    s=burm_alloc_state(u,op,arity);
    SET_STATE(u,s);
    k=0;
    {  		/* con: CNSTT */
      if(burm_cost_code(&c,22,s) && COST_LESS(c,s->cost[burm_con_NT])) {
burm_trace(burm_np, 22, c);         s->cost[burm_con_NT] = c ;
        s->rule.burm_con = 1;
        burm_closure_con(s, c );
      }
    }
    break;
  case 4:		/* BINOP1 */
    s=burm_alloc_state(u,op,arity);
    SET_STATE(u,s);
    k=s->kids;
    children=GET_KIDS(u);
    for(i=0;i<arity;i++)
      k[i]=burm_label1(children[i]);
    if (   /* disp: BINOP1(reg,rc) */
      k[0]->rule.burm_reg && 
      k[1]->rule.burm_rc
    ) {
      if(burm_cost_code(&c,17,s) && COST_LESS(c,s->cost[burm_disp_NT])) {
burm_trace(burm_np, 17, c);         s->cost[burm_disp_NT] = c ;
        s->rule.burm_disp = 3;
      }
    }
    if (   /* disp: BINOP1(con,con) */
      k[0]->rule.burm_con && 
      k[1]->rule.burm_con
    ) {
      if(burm_cost_code(&c,16,s) && COST_LESS(c,s->cost[burm_disp_NT])) {
burm_trace(burm_np, 16, c);         s->cost[burm_disp_NT] = c ;
        s->rule.burm_disp = 2;
      }
    }
    if (   /* reg: BINOP1(reg,rc) */
      k[0]->rule.burm_reg && 
      k[1]->rule.burm_rc
    ) {
      if(burm_cost_code(&c,12,s) && COST_LESS(c,s->cost[burm_reg_NT])) {
burm_trace(burm_np, 12, c);         s->cost[burm_reg_NT] = c ;
        s->rule.burm_reg = 4;
        burm_closure_reg(s, c );
      }
    }
    if (   /* reg: BINOP1(con,con) */
      k[0]->rule.burm_con && 
      k[1]->rule.burm_con
    ) {
      if(burm_cost_code(&c,11,s) && COST_LESS(c,s->cost[burm_reg_NT])) {
burm_trace(burm_np, 11, c);         s->cost[burm_reg_NT] = c ;
        s->rule.burm_reg = 3;
        burm_closure_reg(s, c );
      }
    }
    break;
  case 5:		/* BINOP2 */
    s=burm_alloc_state(u,op,arity);
    SET_STATE(u,s);
    k=s->kids;
    children=GET_KIDS(u);
    for(i=0;i<arity;i++)
      k[i]=burm_label1(children[i]);
    if (   /* disp: BINOP2(rc,reg) */
      k[0]->rule.burm_rc && 
      k[1]->rule.burm_reg
    ) {
      if(burm_cost_code(&c,18,s) && COST_LESS(c,s->cost[burm_disp_NT])) {
burm_trace(burm_np, 18, c);         s->cost[burm_disp_NT] = c ;
        s->rule.burm_disp = 4;
      }
    }
    if (   /* reg: BINOP2(rc,reg) */
      k[0]->rule.burm_rc && 
      k[1]->rule.burm_reg
    ) {
      if(burm_cost_code(&c,13,s) && COST_LESS(c,s->cost[burm_reg_NT])) {
burm_trace(burm_np, 13, c);         s->cost[burm_reg_NT] = c ;
        s->rule.burm_reg = 5;
        burm_closure_reg(s, c );
      }
    }
    break;
  case 6:		/* COPYI */
#ifdef LEAF_TRAP
    if(s=LEAF_TRAP(u,op))
      return s;
#endif
    s=burm_alloc_state(u,op,arity);
    SET_STATE(u,s);
    k=0;
    {  		/* reg: COPYI */
      if(burm_cost_code(&c,10,s) && COST_LESS(c,s->cost[burm_reg_NT])) {
burm_trace(burm_np, 10, c);         s->cost[burm_reg_NT] = c ;
        s->rule.burm_reg = 2;
        burm_closure_reg(s, c );
      }
    }
    break;
  case 7:		/* ADDRLP */
#ifdef LEAF_TRAP
    if(s=LEAF_TRAP(u,op))
      return s;
#endif
    s=burm_alloc_state(u,op,arity);
    SET_STATE(u,s);
    k=0;
    {  		/* disp: ADDRLP */
      if(burm_cost_code(&c,15,s) && COST_LESS(c,s->cost[burm_disp_NT])) {
burm_trace(burm_np, 15, c);         s->cost[burm_disp_NT] = c ;
        s->rule.burm_disp = 1;
      }
    }
    break;
  case 8:		/* ASGNI */
    s=burm_alloc_state(u,op,arity);
    SET_STATE(u,s);
    k=s->kids;
    children=GET_KIDS(u);
    for(i=0;i<arity;i++)
      k[i]=burm_label1(children[i]);
    break;
  case 9:		/* MEM */
    s=burm_alloc_state(u,op,arity);
    SET_STATE(u,s);
    k=s->kids;
    children=GET_KIDS(u);
    for(i=0;i<arity;i++)
      k[i]=burm_label1(children[i]);
    break;
  case 10:		/* STOREI2 */
    s=burm_alloc_state(u,op,arity);
    SET_STATE(u,s);
    k=s->kids;
    children=GET_KIDS(u);
    for(i=0;i<arity;i++)
      k[i]=burm_label1(children[i]);
    if (   /* stmt: STOREI2(disp,disp) */
      k[0]->rule.burm_disp && 
      k[1]->rule.burm_disp
    ) {
      if(burm_cost_code(&c,5,s) && COST_LESS(c,s->cost[burm_stmt_NT])) {
burm_trace(burm_np, 5, c);         s->cost[burm_stmt_NT] = c ;
        s->rule.burm_stmt = 5;
      }
    }
    break;
  case 11:		/* ICMPI */
    s=burm_alloc_state(u,op,arity);
    SET_STATE(u,s);
    k=s->kids;
    children=GET_KIDS(u);
    for(i=0;i<arity;i++)
      k[i]=burm_label1(children[i]);
    if (   /* reg: ICMPI(reg,rc) */
      k[0]->rule.burm_reg && 
      k[1]->rule.burm_rc
    ) {
      if(burm_cost_code(&c,3,s) && COST_LESS(c,s->cost[burm_reg_NT])) {
burm_trace(burm_np, 3, c);         s->cost[burm_reg_NT] = c ;
        s->rule.burm_reg = 1;
        burm_closure_reg(s, c );
      }
    }
    break;
  case 12:		/* JUMPI */
    s=burm_alloc_state(u,op,arity);
    SET_STATE(u,s);
    k=s->kids;
    children=GET_KIDS(u);
    for(i=0;i<arity;i++)
      k[i]=burm_label1(children[i]);
    if (   /* stmt: JUMPI(rc) */
      k[0]->rule.burm_rc
    ) {
      if(burm_cost_code(&c,7,s) && COST_LESS(c,s->cost[burm_stmt_NT])) {
burm_trace(burm_np, 7, c);         s->cost[burm_stmt_NT] = c ;
        s->rule.burm_stmt = 7;
      }
    }
    break;
  case 13:		/* UJUMPI */
#ifdef LEAF_TRAP
    if(s=LEAF_TRAP(u,op))
      return s;
#endif
    s=burm_alloc_state(u,op,arity);
    SET_STATE(u,s);
    k=0;
    {  		/* stmt: UJUMPI */
      if(burm_cost_code(&c,6,s) && COST_LESS(c,s->cost[burm_stmt_NT])) {
burm_trace(burm_np, 6, c);         s->cost[burm_stmt_NT] = c ;
        s->rule.burm_stmt = 6;
      }
    }
    break;
  case 14:		/* GLOBI */
#ifdef LEAF_TRAP
    if(s=LEAF_TRAP(u,op))
      return s;
#endif
    s=burm_alloc_state(u,op,arity);
    SET_STATE(u,s);
    k=0;
    {  		/* disp: GLOBI */
      if(burm_cost_code(&c,19,s) && COST_LESS(c,s->cost[burm_disp_NT])) {
burm_trace(burm_np, 19, c);         s->cost[burm_disp_NT] = c ;
        s->rule.burm_disp = 5;
      }
    }
    break;
  case 15:		/* RETI */
    s=burm_alloc_state(u,op,arity);
    SET_STATE(u,s);
    k=s->kids;
    children=GET_KIDS(u);
    for(i=0;i<arity;i++)
      k[i]=burm_label1(children[i]);
    if (   /* stmt: RETI(reg) */
      k[0]->rule.burm_reg
    ) {
      if(burm_cost_code(&c,9,s) && COST_LESS(c,s->cost[burm_stmt_NT])) {
burm_trace(burm_np, 9, c);         s->cost[burm_stmt_NT] = c ;
        s->rule.burm_stmt = 9;
      }
    }
    break;
  case 16:		/* URET */
#ifdef LEAF_TRAP
    if(s=LEAF_TRAP(u,op))
      return s;
#endif
    s=burm_alloc_state(u,op,arity);
    SET_STATE(u,s);
    k=0;
    {  		/* stmt: URET */
      if(burm_cost_code(&c,1,s) && COST_LESS(c,s->cost[burm_stmt_NT])) {
burm_trace(burm_np, 1, c);         s->cost[burm_stmt_NT] = c ;
        s->rule.burm_stmt = 2;
      }
    }
    break;
  default:
    burm_assert(0, PANIC("Bad operator %d in burm_state\n", op));
  }
  return s;
}

struct burm_state *burm_label(NODEPTR p) {
  burm_label1(p);
  return ((struct burm_state *)STATE_LABEL(p))->rule.burm_stmt ? STATE_LABEL(p) : 0;
}

void burm_free(struct burm_state *s)
{
  int i,arity=burm_arity[s->op];
  if(s->kids==0)
    free(s);
  else {
    for(i=0;i<arity;i++)
      burm_free(s->kids[i]);
    free(s->kids);
  }
}
struct burm_state *burm_immed(struct burm_state *s,int n)
{
  NODEPTR *children = GET_KIDS(s->node);
  if(s->kids[n])
    return s->kids[n];
  else
  return s->kids[n]=burm_label1(children[n]);
}
int burm_op_label(NODEPTR p) {
  burm_assert(p, PANIC("NULL tree in burm_op_label\n"));
  return OP_LABEL(p);
}

struct burm_state *burm_state_label(NODEPTR p) {
  burm_assert(p, PANIC("NULL tree in burm_state_label\n"));
  return STATE_LABEL(p);
}

NODEPTR burm_child(NODEPTR p, int index) {
  NODEPTR *kids;
  burm_assert(p, PANIC("NULL tree in burm_child\n"));
  kids=GET_KIDS(p);
  burm_assert((0<=index && index<burm_arity[OP_LABEL(p)]),
    PANIC("Bad index %d in burm_child\n", index));

  return kids[index];
}
NODEPTR *burm_kids(NODEPTR p, int eruleno, NODEPTR kids[]) {
  burm_assert(p, PANIC("NULL tree in burm_kids\n"));
  burm_assert(kids, PANIC("NULL kids in burm_kids\n"));
  switch (eruleno) {
  case 0: /* stmt: BURP(_,_,_) */
    kids[0] = burm_child(p,0);
    kids[1] = burm_child(p,1);
    kids[2] = burm_child(p,2);
    break;
  case 22: /* con: CNSTT */
  case 19: /* disp: GLOBI */
  case 15: /* disp: ADDRLP */
  case 14: /* reg: LOADI */
  case 10: /* reg: COPYI */
  case 6: /* stmt: UJUMPI */
  case 1: /* stmt: URET */
    break;
  case 18: /* disp: BINOP2(rc,reg) */
  case 17: /* disp: BINOP1(reg,rc) */
  case 16: /* disp: BINOP1(con,con) */
  case 13: /* reg: BINOP2(rc,reg) */
  case 12: /* reg: BINOP1(reg,rc) */
  case 11: /* reg: BINOP1(con,con) */
  case 5: /* stmt: STOREI2(disp,disp) */
  case 4: /* stmt: STOREI(reg,rc) */
  case 3: /* reg: ICMPI(reg,rc) */
  case 2: /* stmt: STOREI(disp,rc) */
    kids[0] = burm_child(p,0);
    kids[1] = burm_child(p,1);
    break;
  case 9: /* stmt: RETI(reg) */
  case 7: /* stmt: JUMPI(rc) */
    kids[0] = burm_child(p,0);
    break;
  case 21: /* rc: reg */
  case 20: /* rc: con */
  case 8: /* stmt: reg */
    kids[0] = p;
    break;
  default:
    burm_assert(0, PANIC("Bad external rule number %d in burm_kids\n", eruleno));
  }
  return kids;
}

void dumpCover(NODEPTR p, int goalnt, int indent)
{
  int eruleno = burm_rule(STATE_LABEL(p), goalnt);
  short *nts = burm_nts[eruleno];
  NODEPTR kids[10];
  int i;

  std::cerr << "\t\t";
  for (i = 0; i < indent; i++)
    std::cerr << " ";
  std::cerr << burm_string[eruleno] << "\n";
  burm_kids(p, eruleno, kids);
  for (i = 0; nts[i]; i++)
    dumpCover(kids[i], nts[i], indent + 1);
}


#pragma GCC diagnostic pop



/* burm_trace - print trace message for matching p */
static void burm_trace(NODEPTR p, int eruleno, COST cost) {
	if (shouldTrace)
		std::cerr << "0x" << p << " matched " << burm_string[eruleno] << " = " << eruleno << " with cost " << cost.cost << "\n";
}

static void gen(NODEPTR p) {
	if (burm_label(p) == 0)
		std::cerr << "no cover\n";
	else {
		stmt_action(p->x.state,0);
		if (shouldCover != 0)
			dumpCover(p, 1, 0);
	}
}

static void updateLifeInterval(NODEPTR p) {
  p->start = InstIdx[p->inst];
  p->end = 0;

  for (int i = 0; i < p->inst->getNumOperands(); ++i)
  {
    if (isa<Constant>(p->inst->getOperand(i)))
      continue;

    if (!isa<Instruction>(p->inst->getOperand(i)))
      continue;

    Instruction* opinst = dyn_cast<Instruction>(p->inst->getOperand(i));
    if (nodes.find(opinst) != nodes.end())
      nodes[opinst]->end = p->start;
    if (roots.find(opinst) != roots.end())
      roots[opinst]->end = p->start;
  }
}

// Generate the layout for all global data
static void GlobalLayOut()
{
  bool flag = true;
  std::vector<Instruction*> cvec;

  std::cout << "\n";
  for (auto inst : gvec)
  {
    std::string str;
    llvm::raw_string_ostream rso(str);
    inst->print(rso);
    rso.flush();

    std::stringstream ss(str);
    std::string var;
    std::string tmp;
    std::string ope;
    ss >> var >> tmp >> ope;
    if (ope.compare("common") == 0)
    {
      cvec.push_back(inst);
      continue;
    }

    var.erase(var.begin());
    Constant* cnst = dyn_cast<Constant>(inst->getOperand(0));
    int val = cnst->getUniqueInteger().getSExtValue();
    std::cout << "\t.type\t" << var << ",@object\n";
    if (flag)
    {
      std::cout << "\t.data\n";
      flag = false;
    }
    std::cout << "\t.globl\t" << var << "\n";
    std::cout << "\t.align\t" << "8\n";
    std::cout << var << ":\n";
    std::cout << "\t.quad\t" << val << "\n";
    std::cout << "\t.size\t" << var << ", 8\n\n";
  }

  for (auto inst : cvec)
  {
    std::string str;
    llvm::raw_string_ostream rso(str);
    inst->print(rso);
    rso.flush();
    
    std::stringstream ss(str);
    std::string var;
    ss >> var;
    var.erase(var.begin());
    std::cout << "\t.type\t" << var << ",@object\n";
    std::cout << "\t.comm\t" << var << ",8,8\n";
  }

}

/* Generate the header for the assembly code */
void headerGen(char *filename)
{ 
  std::cout << "\t.text\n";
  std::cout << "\t.file\t" << "\"" << filename << "\"\n";
  std::cout << "\t.global\tmain\n";
  std::cout << "\t.align\t16, 0x90\n";
  std::cout << "\t.type\tmain,@function\n";
  std::cout << "main:\n";
  std::cout << "\tpushq\t%rbp\n";
  std::cout << "\tmovq\t%rsp, %rbp\n";
}

/* Generate the tail for the assembly code */
void tailGen()
{
  //std::cout << "\txorl\t%eax, %eax\n";
  //std::cout << "\tmovq\t-8(%rbp), %rax\n";
  std::cout << "\tpopq\t%rbp\n";
  std::cout << "\tretq\n";
}
#endif
