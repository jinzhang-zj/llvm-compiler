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
enum {
  LOADI=1, STOREI=2, CNSTT=3, ADDI1=4,
  ADDI2=5, STOREI2=10,
  COPYI=6, ADDRLP=7, ASGNI=8, MEM=9
};

typedef struct tree {
  int op;
  int inst_num;
  struct tree *kids[2];
  int val;
  int start;
  int end;
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
std::map<Instruction*, int> SymTable;	// Instruction and offset in stack
std::map<Instruction*, int> InstIdx;	// Instruction and its number
std::map<Instruction*, std::string> RegTable;  // Instruction and register
std::map<std::string, Instruction*> InsTable;  // Register and instruction

int offCount = 0;	// Global value for offset count

static std::string getNexReg(Instruction *inst) {
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
  }
  //errs() << "\ninstruction " << *inst << " is getting " << reg << "\n";
  return reg;
}

static int getNexOff()
{
  offCount += 8;
  return offCount - 8;
}

#define BURP 0
#define LOADI 1
#define STOREI 2
#define CNSTT 3
#define ADDI1 4
#define ADDI2 5
#define COPYI 6
#define ADDRLP 7
#define ASGNI 8
#define MEM 9
#define STOREI2 10
#define RETI 11

struct burm_state {
  int op;
  NODEPTR node;
  struct burm_state **kids;
  COST cost[7];
  struct {
    unsigned burm_stmt:3;
    unsigned burm_reg:2;
    unsigned burm_disp:2;
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
static short burm_nts_1[] = { burm_disp_NT, burm_rc_NT, 0 };
static short burm_nts_2[] = { burm_reg_NT, burm_rc_NT, 0 };
static short burm_nts_3[] = { burm_disp_NT, burm_disp_NT, 0 };
static short burm_nts_4[] = { burm_reg_NT, 0 };
static short burm_nts_5[] = { 0 };
static short burm_nts_6[] = { burm_con_NT, 0 };

short *burm_nts[] = {
  burm_nts_0,  /* 0 */
  burm_nts_1,  /* 1 */
  burm_nts_2,  /* 2 */
  burm_nts_3,  /* 3 */
  burm_nts_4,  /* 4 */
  burm_nts_5,  /* 5 */
  burm_nts_2,  /* 6 */
  burm_nts_5,  /* 7 */
  burm_nts_5,  /* 8 */
  burm_nts_2,  /* 9 */
  burm_nts_6,  /* 10 */
  burm_nts_4,  /* 11 */
  burm_nts_5,  /* 12 */
};

char burm_arity[] = {
  3,  /* 0=BURP */
  0,  /* 1=LOADI */
  2,  /* 2=STOREI */
  0,  /* 3=CNSTT */
  2,  /* 4=ADDI1 */
  0,  /* 5=ADDI2 */
  0,  /* 6=COPYI */
  0,  /* 7=ADDRLP */
  0,  /* 8=ASGNI */
  0,  /* 9=MEM */
  2,  /* 10=STOREI2 */
  0,  /* 11=RETI */
};

std::string burm_opname[] = {
  /* 0 */  "BURP",
  /* 1 */  "LOADI",
  /* 2 */  "STOREI",
  /* 3 */  "CNSTT",
  /* 4 */  "ADDI1",
  /* 5 */  "ADDI2",
  /* 6 */  "COPYI",
  /* 7 */  "ADDRLP",
  /* 8 */  "ASGNI",
  /* 9 */  "MEM",
  /* 10 */  "STOREI2",
  /* 11 */  "RETI",
};


std::string burm_string[] = {
  /* 0 */  "stmt: BURP(_,_,_)",
  /* 1 */  "stmt: STOREI(disp,rc)",
  /* 2 */  "stmt: STOREI(reg,rc)",
  /* 3 */  "stmt: STOREI2(disp,disp)",
  /* 4 */  "stmt: reg",
  /* 5 */  "reg: COPYI",
  /* 6 */  "reg: ADDI1(reg,rc)",
  /* 7 */  "reg: LOADI",
  /* 8 */  "disp: ADDRLP",
  /* 9 */  "disp: ADDI1(reg,rc)",
  /* 10 */  "rc: con",
  /* 11 */  "rc: reg",
  /* 12 */  "con: CNSTT",
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
};

int burm_line_numbers[] = {
  /* 0 */  112,
  /* 1 */  119,
  /* 2 */  130,
  /* 3 */  141,
  /* 4 */  156,
  /* 5 */  166,
  /* 6 */  180,
  /* 7 */  194,
  /* 8 */  211,
  /* 9 */  235,
  /* 10 */  250,
  /* 11 */  260,
  /* 12 */  270,
};

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-variable"

static short burm_decode_stmt[] = {
   -1,
  0,
  1,
  2,
  3,
  4,
};

static short burm_decode_reg[] = {
   -1,
  5,
  6,
  7,
};

static short burm_decode_disp[] = {
   -1,
  8,
  9,
};

static short burm_decode_rc[] = {
   -1,
  10,
  11,
};

static short burm_decode_con[] = {
   -1,
  12,
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


 (*_c).cost=_s->kids[0]->cost[burm_disp_NT].cost+_s->kids[1]->cost[burm_rc_NT].cost+1; 
}
  break;
  case 2:
{


 (*_c).cost=_s->kids[0]->cost[burm_reg_NT].cost+_s->kids[1]->cost[burm_rc_NT].cost+1; 
}
  break;
  case 3:
{


 (*_c).cost=_s->kids[0]->cost[burm_disp_NT].cost+_s->kids[1]->cost[burm_disp_NT].cost+1; 
}
  break;
  case 4:
{


 (*_c).cost=_s->cost[burm_reg_NT].cost; 
}
  break;
  case 5:
{


 (*_c).cost=1; 
}
  break;
  case 6:
{


 (*_c).cost=_s->kids[0]->cost[burm_reg_NT].cost+_s->kids[1]->cost[burm_rc_NT].cost+1; 
}
  break;
  case 7:
{


 (*_c).cost=1; 
}
  break;
  case 8:
{


 (*_c).cost=0; 
}
  break;
  case 9:
{


 (*_c).cost=_s->kids[0]->cost[burm_reg_NT].cost+_s->kids[1]->cost[burm_rc_NT].cost+1; 
}
  break;
  case 10:
{


 (*_c).cost=_s->cost[burm_con_NT].cost; 
}
  break;
  case 11:
{


 (*_c).cost=_s->cost[burm_reg_NT].cost; 
}
  break;
  case 12:
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
		std::cout << "movq " + disp_action(_s->kids[0],indent+1) + ", " + rc_action(_s->kids[1],indent+1) + "\n";
		return "";
	
}
  break;
  case 2:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
		std::cout << "movq (" + reg_action(_s->kids[0],indent+1) + "), " + rc_action(_s->kids[1],indent+1) + "\n";
		return "";
	
}
  break;
  case 3:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
                std::string reg1 = getNexReg(_s->node->inst);
		RegTable[_s->node->inst] = reg1;
                InsTable[reg1] = _s->node->inst;
                std::cout << "leaq " << reg1 << ", " << disp_action(_s->kids[1],indent+1) << "\n";
		std::cout << "movq " + disp_action(_s->kids[0],indent+1) + ", " + reg1 + "\n";
		return "";
	
}
  break;
  case 4:
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


std::string reg_action(struct burm_state *_s, 

int indent)
{
  struct burm_state *_t;
  int _ern=burm_decode_reg[_s->rule.burm_reg];
  NODEPTR *_children;
  if(_s->rule.burm_reg==0)
    NO_ACTION(reg);
  switch(_ern){
  case 5:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
                std::string reg1 = getNexReg(_s->node->inst);
		RegTable[_s->node->inst] = reg1;
                InsTable[reg1] = _s->node->inst;
                std::cout << "movq " + reg1 + ", " + RegTable[_s->node->inst] + "\n";
                return reg1;
	
}
  break;
  case 6:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
                std::string reg1 = reg_action(_s->kids[0],indent+1);
                std::cout << "addq " + reg1 +  ", " + rc_action(_s->kids[1],indent+1) + "\n";
                NODEPTR cur = _s->node;
                RegTable[cur->inst] = reg1;
                return reg1;
	
}
  break;
  case 7:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
                std::string reg1 = getNexReg(_s->node->inst);
		RegTable[_s->node->inst] = reg1;
                InsTable[reg1] = _s->node->inst;
                NODEPTR cur = _s->node;
                Instruction *inst = dyn_cast<Instruction>(cur->inst->getOperand(0));
                int offset = SymTable[inst];
                std::cout << "movq " + reg1 + ", " + std::to_string(offset) + "(%rbp)\n";
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
  case 8:
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
  case 9:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
                std::string reg1 = reg_action(_s->kids[0],indent+1);
                std::cout << "addq " + reg1 +  ", " + rc_action(_s->kids[1],indent+1) + "\n";
                NODEPTR cur = _s->node;
                RegTable[cur->inst] = reg1;
                return reg1;
	
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
  case 10:
{



		int i;
		for (i = 0; i < indent; i++)
			std::cerr << " ";
		std::cerr << burm_string[_ern] << "\n";
		return con_action(_s,indent+1);
	
}
  break;
  case 11:
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
  case 12:
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
  if(burm_cost_code(&c,11,s) && COST_LESS(c,s->cost[burm_rc_NT])) {
burm_trace(burm_np, 11, c);     s->cost[burm_rc_NT] = c ;
    s->rule.burm_rc = 2;
  }
  if(burm_cost_code(&c,4,s) && COST_LESS(c,s->cost[burm_stmt_NT])) {
burm_trace(burm_np, 4, c);     s->cost[burm_stmt_NT] = c ;
    s->rule.burm_stmt = 5;
  }
}

static void burm_closure_con(struct burm_state *s, COST c) {
  if(burm_cost_code(&c,10,s) && COST_LESS(c,s->cost[burm_rc_NT])) {
burm_trace(burm_np, 10, c);     s->cost[burm_rc_NT] = c ;
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
      if(burm_cost_code(&c,7,s) && COST_LESS(c,s->cost[burm_reg_NT])) {
burm_trace(burm_np, 7, c);         s->cost[burm_reg_NT] = c ;
        s->rule.burm_reg = 3;
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
      if(burm_cost_code(&c,2,s) && COST_LESS(c,s->cost[burm_stmt_NT])) {
burm_trace(burm_np, 2, c);         s->cost[burm_stmt_NT] = c ;
        s->rule.burm_stmt = 3;
      }
    }
    if (   /* stmt: STOREI(disp,rc) */
      k[0]->rule.burm_disp && 
      k[1]->rule.burm_rc
    ) {
      if(burm_cost_code(&c,1,s) && COST_LESS(c,s->cost[burm_stmt_NT])) {
burm_trace(burm_np, 1, c);         s->cost[burm_stmt_NT] = c ;
        s->rule.burm_stmt = 2;
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
      if(burm_cost_code(&c,12,s) && COST_LESS(c,s->cost[burm_con_NT])) {
burm_trace(burm_np, 12, c);         s->cost[burm_con_NT] = c ;
        s->rule.burm_con = 1;
        burm_closure_con(s, c );
      }
    }
    break;
  case 4:		/* ADDI1 */
    s=burm_alloc_state(u,op,arity);
    SET_STATE(u,s);
    k=s->kids;
    children=GET_KIDS(u);
    for(i=0;i<arity;i++)
      k[i]=burm_label1(children[i]);
    if (   /* disp: ADDI1(reg,rc) */
      k[0]->rule.burm_reg && 
      k[1]->rule.burm_rc
    ) {
      if(burm_cost_code(&c,9,s) && COST_LESS(c,s->cost[burm_disp_NT])) {
burm_trace(burm_np, 9, c);         s->cost[burm_disp_NT] = c ;
        s->rule.burm_disp = 2;
      }
    }
    if (   /* reg: ADDI1(reg,rc) */
      k[0]->rule.burm_reg && 
      k[1]->rule.burm_rc
    ) {
      if(burm_cost_code(&c,6,s) && COST_LESS(c,s->cost[burm_reg_NT])) {
burm_trace(burm_np, 6, c);         s->cost[burm_reg_NT] = c ;
        s->rule.burm_reg = 2;
        burm_closure_reg(s, c );
      }
    }
    break;
  case 5:		/* ADDI2 */
    s=burm_alloc_state(u,op,arity);
    SET_STATE(u,s);
    k=s->kids;
    children=GET_KIDS(u);
    for(i=0;i<arity;i++)
      k[i]=burm_label1(children[i]);
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
      if(burm_cost_code(&c,5,s) && COST_LESS(c,s->cost[burm_reg_NT])) {
burm_trace(burm_np, 5, c);         s->cost[burm_reg_NT] = c ;
        s->rule.burm_reg = 1;
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
      if(burm_cost_code(&c,8,s) && COST_LESS(c,s->cost[burm_disp_NT])) {
burm_trace(burm_np, 8, c);         s->cost[burm_disp_NT] = c ;
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
      if(burm_cost_code(&c,3,s) && COST_LESS(c,s->cost[burm_stmt_NT])) {
burm_trace(burm_np, 3, c);         s->cost[burm_stmt_NT] = c ;
        s->rule.burm_stmt = 4;
      }
    }
    break;
  case 11:		/* RETI */
    s=burm_alloc_state(u,op,arity);
    SET_STATE(u,s);
    k=s->kids;
    children=GET_KIDS(u);
    for(i=0;i<arity;i++)
      k[i]=burm_label1(children[i]);
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
  case 9: /* disp: ADDI1(reg,rc) */
  case 6: /* reg: ADDI1(reg,rc) */
  case 3: /* stmt: STOREI2(disp,disp) */
  case 2: /* stmt: STOREI(reg,rc) */
  case 1: /* stmt: STOREI(disp,rc) */
    kids[0] = burm_child(p,0);
    kids[1] = burm_child(p,1);
    break;
  case 11: /* rc: reg */
  case 10: /* rc: con */
  case 4: /* stmt: reg */
    kids[0] = p;
    break;
  case 12: /* con: CNSTT */
  case 8: /* disp: ADDRLP */
  case 7: /* reg: LOADI */
  case 5: /* reg: COPYI */
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
    if (isa<Constant>(p->inst->getOperand(0)))
      continue;

    Instruction* opinst = dyn_cast<Instruction>(p->inst->getOperand(i));
    if (nodes.find(opinst) != nodes.end())
      nodes[opinst]->end = p->start;
    if (roots.find(opinst) != roots.end())
      roots[opinst]->end = p->start;
  }
}
#endif
