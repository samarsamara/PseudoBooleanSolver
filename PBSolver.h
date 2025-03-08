#pragma once
#include <iostream>
#include <algorithm>
#include <iterator>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <map>
#include <set>
#include <string>
#include <sstream>
#include <fstream>
#include <cassert>
#include <ctime>
#include "options.h"
using namespace std;

typedef int Var;
typedef int Lit;
typedef vector<Lit> clause_t;
typedef clause_t::iterator clause_it;
typedef vector<Lit> trail_t;

#define Assert(exp) AssertCheck(exp, __func__, __LINE__)


#define Neg(l) (l & 1)
#define Restart_multiplier 1.1f
#define Restart_lower 100
#define Restart_upper 1000
#define Max_bring_forward 10
#define var_decay 0.99
#define Rescale_threshold 1e100
#define Assignment_file "assignment.txt"

int verbose = 0;
double begin_time;
double timeout = 0.0;


void Abort(string s, int i);

enum class VAR_DEC_HEURISTIC {
	MINISAT
	// add other decision heuristics here. Add an option to choose between them.
};

VAR_DEC_HEURISTIC VarDecHeuristic = VAR_DEC_HEURISTIC::MINISAT;

enum class VAL_DEC_HEURISTIC {
	/* Same as last value. Initially false*/
	PHASESAVING,
	/* Choose literal with highest frequency */
	LITSCORE
};

VAL_DEC_HEURISTIC ValDecHeuristic = VAL_DEC_HEURISTIC::PHASESAVING;


unordered_map<string, option*> options = {
	{"v",           new intoption(&verbose, 0, 2, "Verbosity level")},
	{"timeout",     new doubleoption(&timeout, 0.0, 36000.0, "Timeout in seconds")},
	{"valdh",       new intoption((int*)&ValDecHeuristic, 0, 1, "{0: phase-saving, 1: literal-score}")}
};


enum class LitState {
	L_UNSAT,
	L_SAT,
	L_UNASSIGNED
};

enum class VarState {
	V_FALSE,
	V_TRUE,
	V_UNASSIGNED
};

enum class ClauseState {
	C_UNSAT,
	C_SAT,
	C_UNIT,
	C_UNDEF
};

enum class PBConstraintState {
	PB_UNDEF,
	PB_SAT,
	PB_UNIT,
	PB_UNSAT
};

enum class SolverState {
	UNSAT,
	SAT,
	CONFLICT,
	UNDEF,
	TIMEOUT
};
/***************** service functions **********************/

#ifdef _MSC_VER
#include <ctime>

static inline double cpuTime(void) {
	return (double)clock() / CLOCKS_PER_SEC;
}
#else

#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>

static inline double cpuTime(void) {
	struct rusage ru;
	getrusage(RUSAGE_SELF, &ru);
	return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000;
}
#endif

// For production wrap with #ifdef _DEBUG
void AssertCheck(bool cond, string func_name, int line, string msg = "") {
	if (cond) return;
	cout << "Assertion fail" << endl;
	cout << msg << endl;
	cout << func_name << " line " << line << endl;
	exit(1);
}


bool match(ifstream& in, char* str) {
	for (; *str != '\0'; ++str)
		if (*str != in.get())
			return false;
	return true;
}

unsigned int Abs(int x) { // because the result is compared to an unsigned int. unsigned int are introduced by size() functions, that return size_t, which is defined to be unsigned. 
	if (x < 0) return (unsigned int)-x;
	else return (unsigned int)x;
}

unsigned int v2l(int i) { // maps a literal as it appears in the cnf to literal
	if (i < 0) return ((-i) << 1) - 1;
	else return i << 1;
}

Var l2v(Lit l) {
	return (l + 1) / 2;
}

Lit negate(Lit l) {
	if (Neg(l)) return l + 1;  // odd
	return l - 1;
}

int l2rl(int l) {
	return Neg(l) ? -((l + 1) / 2) : l / 2;
}


/********** classes ******/

class Constraint {
	std::vector<std::pair<int, int>> terms;
	clause_t literals;       // 
	std::vector<int> coefficients; //
	int rhs;
	int lhs;
	int lw, rw; //watches;
	std::unordered_set<int> watch_set; // Set of watched literals (minimum size 2)
	bool flag_new; // used in Backtrack() to indicate that the constraint was learned in the current decision level.
public:
	Constraint() { lhs = 0;};
	void insert_term(int coeff, Lit var) {
		terms.emplace_back(coeff, var);
		literals.push_back(var);
		coefficients.push_back(coeff);
	}
	void print_real_lits() {
		Lit l;
		cout << "(";
		for (clause_it it = literals.begin(); it != literals.end(); ++it) {
			l = l2rl(*it);
			cout << l << " ";
		} cout << ")";
	}
	void set_watches_set(std::unordered_set<int> watches) { watch_set = watches; }
    void lw_set(int i) { lw = i; /*assert(lw != rw);*/ }
	void rw_set(int i) { rw = i; /*assert(lw != rw);*/ }
	std::vector<std::pair<int, int>> get_terms() { return terms; }
	clause_t& get_literals() { return literals; }
	std::vector<int>& get_coefficients() { return coefficients; }
	void reset_literals() { literals.clear();}
	void reset_coefficients() { coefficients.clear(); }
	void reset_terms() { terms.clear(); }
	void set_flag_new(bool b) { flag_new = b; }
	bool get_flag_new() { return flag_new; }
	int get_lw() { return lw; }
	std::unordered_set<int> get_watch_set() { return watch_set; }
	int get_rw() { return rw; }
	void set_rhs(int v) { rhs = v; }
	int get_rhs() { return rhs; }
	void set_lhs(int v) { lhs = v; }
	int get_lhs() { return lhs; }
	int get_lw_lit() const { return literals[lw]; }
	int get_rw_lit() const { return literals[rw]; }
	int lit(int i) const { return literals[i]; }
	size_t constraint_size() const { return literals.size(); }
	inline PBConstraintState Constraint::next_not_false(bool is_left_watch, Lit other_watch, bool binary, int& loc);


	
	void print_constraint() const {
		for (size_t i = 0; i < literals.size(); ++i) {
			std::cout << coefficients[i] << "*x" << literals[i] << " + ";
		}
		std::cout << "<= " << rhs << std::endl;
	}

	// Print with watched literals
	void print_with_watches() const {
		for (size_t i = 0; i < literals.size(); ++i) {
			std::cout << l2rl(literals[i]);
			if (i == lw) std::cout << "L";
			if (i == rw) std::cout << "R";
			std::cout << " ";
		}
		std::cout << "<= " << rhs << std::endl;
	}


};


class Clause {
	clause_t c;
	int lw, rw; //watches;	
public:
	Clause() {};
	void insert(int i) { c.push_back(i); }
	void lw_set(int i) { lw = i; /*assert(lw != rw);*/ }
	void rw_set(int i) { rw = i; /*assert(lw != rw);*/ }
	clause_t& cl() { return c; }
	int get_lw() { return lw; }
	int get_rw() { return rw; }
	int get_lw_lit() { return c[lw]; }
	int get_rw_lit() { return c[rw]; }
	int  lit(int i) { return c[i]; }
	inline ClauseState next_not_false(bool is_left_watch, Lit other_watch, bool binary, int& loc);
	size_t size() { return c.size(); }
	void reset() { c.clear(); }
	void print() { for (clause_it it = c.begin(); it != c.end(); ++it) { cout << *it << " "; }; }
	void print_real_lits() {
		Lit l;
		cout << "(";
		for (clause_it it = c.begin(); it != c.end(); ++it) {
			l = l2rl(*it);
			cout << l << " ";
		} cout << ")";
	}
	void print_with_watches() {
		for (clause_it it = c.begin(); it != c.end(); ++it) {
			cout << l2rl(*it);
			int j = distance(c.begin(), it); //also could write "int j = i - c.begin();"  : the '-' operator is overloaded to allow such things. but distance is more standard, as it works on all standard containers.
			if (j == lw) cout << "L";
			if (j == rw) cout << "R";
			cout << " ";
		};
	}
};

class PBSolver {
	vector<Constraint> unaries;
	trail_t trail_pb; // assignment stack for pb
	vector<int> separators; // indices into trail showing increase in dl 	
	vector<int> LitScore; // literal => frequency of this literal (# appearances in all clauses). 
	vector<vector<int> > watches;  // Lit => vector of clause indices into CNF
	vector<VarState> state_pb;// current assignment
	vector<VarState> prev_state_pb;
	vector<int> antecedent; // var => clause index in the cnf vector. For variables that their value was assigned in BCP, this is the clause that gave this variable its value. 
	vector<bool> marked;	// var => seen during analyze()
	vector<int> dlevel_pb;
	vector<int> conflicts_at_dl; // decision level => # of conflicts under it. Used for local restarts. 
	vector<int> reason_pb; //track each lit propagate based on what constriant 
	vector<Constraint> pbConstraints;  // Store PB constraints
	unordered_map<int, std::vector<int>> var_to_pb_constraints;
	unordered_map<int, int> var_occurrence_count; // Maps var ? count of occurrences
	unordered_set<int> assigned_vars;
	std::unordered_set<std::string> constraint_set;


	// Used by VAR_DH_MINISAT:	
	map<double, unordered_set<Var>, greater<double>> m_Score2Vars; // 'greater' forces an order from large to small of the keys
	map<double, unordered_set<Var>, greater<double>>::iterator m_Score2Vars_it;
	unordered_set<Var>::iterator m_VarsSameScore_it;
	vector<double>	m_activity; // Var => activity
	double			m_var_inc;	// current increment of var score (it increases over time)
	double			m_curr_activity;
	bool			m_should_reset_iterators;
	bool            unsat = false;

	unsigned int
		nvars,			// # vars
		nconstraints, 		// # nconstraints
		noldconstraints,	// # nconstraints before adding the new ones
		nlits,			// # literals = 2*nvars				
		qhead;			// index into trail. Used in BCP() to follow the propagation process.
	int
		num_learned,
		num_decisions,
		num_assignments,
		num_restarts,
		dl_pb,// decision level
		max_dl,			// max dl seen so far since the last restart
		conflicting_constraint_idx, // holds the index of the current conflicting clause in cnf[]. -1 if none.				
		restart_threshold,
		restart_lower,
		restart_upper;

	Lit 		asserted_lit;

	float restart_multiplier;

	// access	
	int get_learned() { return num_learned; }
	void set_nvars(int x) { nvars = x; }
	int get_nvars() { return nvars; }
	void set_nconstraints(int x) { nconstraints = x; }
	void set_noldconstraints(int x) { noldconstraints = x; }
	size_t pbConstraints_size() { return pbConstraints.size(); }
	VarState get_state_pb(int x) { return state_pb[x]; }
	void set_state_pb(int x, VarState y) { state_pb[x] = y; }

	// misc.
	void add_to_trail(int x) { trail_pb.push_back(x); }

	void reset(); // initialization that is invoked initially + every restart
	void initialize();
	void reset_iterators(double activity_key = 0.0);

	// solving	
	SolverState decide();
	void test();
	SolverState BCP();
	int analyze(const Constraint& conflictConstraint);
	inline int  getVal(Var v);
	inline void add_constraint(Constraint& c, int l, int r);
	inline void add_unary_constraint(Constraint c);
	inline void assert_lit(Lit l);
	void m_rescaleScores(double& new_score);
	inline void backtrack(int k);
	void restart();
	void normalizePBConstraint(Constraint& pb_constraint, bool bigger);	
	Constraint findConflictSubset(Constraint constraint);
	void print_variable_count(int var);

	// scores	
	inline void bumpVarScore(int idx);
	inline void bumpLitScore(int lit_idx);

public:
	PBSolver() :
		nvars(0), nconstraints(0), num_learned(0), num_decisions(0), num_assignments(0),
		num_restarts(0), m_var_inc(1.0), qhead(0),
		restart_threshold(Restart_lower), restart_lower(Restart_lower),
		restart_upper(Restart_upper), restart_multiplier(Restart_multiplier) {
	};

    inline LitState lit_state(Lit l) {
        VarState var_state = state_pb[l2v(l)];
        return var_state == VarState::V_UNASSIGNED ? LitState::L_UNASSIGNED : (Neg(l) && var_state == VarState::V_FALSE || !Neg(l) && var_state == VarState::V_TRUE) ? LitState::L_SAT : LitState::L_UNSAT;
    }
	inline LitState lit_state(Lit l, VarState var_state) {
		return var_state == VarState::V_UNASSIGNED ? LitState::L_UNASSIGNED : (Neg(l) && var_state == VarState::V_FALSE || !Neg(l) && var_state == VarState::V_TRUE) ? LitState::L_SAT : LitState::L_UNSAT;
	}
	// Function to read pseudo-Boolean constraints
	void read_pb(ifstream& in);
	SolverState _solve();
	void solve();
	void validate_assignment();

	void print_stats() {
		cout << endl << "Statistics: " << endl << "===================" << endl <<
			"### Restarts:\t\t" << num_restarts << endl <<
			"### Learned-clauses:\t" << num_learned << endl <<
			"### Decisions:\t\t" << num_decisions << endl <<
			"### Implications:\t" << num_assignments - num_decisions << endl <<
			"### Time:\t\t" << cpuTime() - begin_time << endl;
	}

	void print_state(const char* file_name) {
		ofstream out;
		out.open(file_name);
		out << "State: ";
		for (vector<VarState>::iterator it = state_pb.begin() + 1; it != state_pb.end(); ++it) {
			char sign = (*it) == VarState::V_FALSE ? -1 : (*it) == VarState::V_TRUE ? 1 : 0;
			out << sign * (it - state_pb.begin()) << " "; out << endl;
		}
	}

	void print_state() {
		cout << "State: ";
		for (vector<VarState>::iterator it = state_pb.begin() + 1; it != state_pb.end(); ++it) {
			char sign = (*it) == VarState::V_FALSE ? -1 : (*it) == VarState::V_TRUE ? 1 : 0;
			cout << sign * (it - state_pb.begin()) << " "; cout << endl;
		}
	}

	void print_watches() {
		for (vector<vector<int> >::iterator it = watches.begin() + 1; it != watches.end(); ++it) {
			cout << distance(watches.begin(), it) << ": ";
			for (vector<int>::iterator it_c = (*it).begin(); it_c != (*it).end(); ++it_c) {
				pbConstraints[*it_c].print_constraint();
				cout << "; ";
			}
			cout << endl;
		}


	};

};
