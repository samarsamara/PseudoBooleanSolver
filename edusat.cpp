#include "edusat.h"


Solver S;

using namespace std;

inline bool verbose_now() {
	return verbose > 1;
}


int Solver::create_variable() {
	return ++variable_count; // Increment and return a new variable index
}


//void Solver::read_pb(std::ifstream& in) {
//	int vars, constraints;
//	in >> vars >> constraints;
//	set_nvars(vars);
//
//	for (int i = 0; i < constraints; ++i) {
//		std::vector<std::pair<int, int>> terms; // Coefficient and variable
//		int rhs;
//		char op;
//
//		// Parse coefficients and variables
//		while (in.peek() != '<' && in.peek() != EOF) {
//			int coeff, var;
//			in >> coeff >> var;
//			terms.emplace_back(coeff, var);
//		}
//
//		// Parse operator and RHS
//		in >> op >> rhs;
//
//		// Convert PB constraint to CNF
//		std::vector<Clause> cnf_clauses = convert_pb_to_cnf(terms, rhs);
//		for (Clause& c : cnf_clauses) {
//			add_clause(c, 0, 1); // Add each generated CNF clause to the solver
//		}
//	}
//}


std::vector<Clause> Solver::convert_pb_to_cnf(const std::vector<std::pair<int, int>>& terms, int rhs) {
	std::vector<Clause> cnf_clauses;

	// Step 1: Initialize buckets
	int max_bits = 0;
	for (const auto& term : terms) {
		int coeff = term.first;
		while (coeff > 0) {
			coeff >>= 1;
			max_bits++;
		}
	}
	std::vector<std::vector<int>> buckets(max_bits);

	// Step 2: Fill the buckets
	for (const auto& term : terms) {
		int coeff = term.first; // Coefficient
		create_variable();
		int var = term.second;  // Variable
		int bit_position = 0;

		while (coeff > 0) {
			if (coeff & 1) {
				buckets[bit_position].push_back(var);
			}
			coeff >>= 1;
			bit_position++;
		}
	}

	// Step 3: Build the adder tree
	for (int i = 0; i < buckets.size(); ++i) {
		std::cout << i <<  std::endl;
		print_buckets(buckets);
		while (buckets[i].size() >= 3) {
			int a = buckets[i].back(); buckets[i].pop_back();
			int b = buckets[i].back(); buckets[i].pop_back();
			int c = buckets[i].back(); buckets[i].pop_back();

			int sum = create_variable();
			int carry = create_variable();

			cnf_clauses = add_full_adder_clauses(a, b, c, sum, carry);

			buckets[i + 1].push_back(carry);
			buckets[i].push_back(sum);
		}

		if (buckets[i].size() == 2) {
			int a = buckets[i].back(); buckets[i].pop_back();
			int b = buckets[i].back(); buckets[i].pop_back();

			int sum = create_variable();
			int carry = create_variable();

			add_half_adder_clauses(a, b, sum, carry);

			buckets[i + 1].push_back(carry);
			buckets[i].push_back(sum);
		}
	}

	// Step 4: Enforce RHS constraint
	for (int i = rhs + 1; i < buckets.size(); ++i) {
		for (int bit : buckets[i]) {
			Clause c;
			c.insert(-bit); // Negate the bit
			cnf_clauses.push_back(c);
		}
	}

	return cnf_clauses;
}

std::vector<Clause> Solver::add_full_adder_clauses(int a, int b, int c_in, int sum, int c_out) {
	// Sum bit clauses
	std::vector<Clause> clauses;
	Clause c1; // ¬a ∨ ¬b ∨ ¬c_in ∨ s
	c1.insert(-a);
	c1.insert(-b);
	c1.insert(-c_in);
	c1.insert(sum);
	clauses.push_back(c1);

	Clause c2; // a ∨ b ∨ ¬s
	c2.insert(a);
	c2.insert(b);
	c2.insert(-sum);
	clauses.push_back(c2);

	Clause c3; // b ∨ c_in ∨ ¬s
	c3.insert(b);
	c3.insert(c_in);
	c3.insert(-sum);
	clauses.push_back(c3);

	Clause c4; // c_in ∨ a ∨ ¬s
	c4.insert(c_in);
	c4.insert(a);
	c4.insert(-sum);
	clauses.push_back(c4);

	// Carry-out bit clauses
	Clause c5; // ¬a ∨ ¬b ∨ c_out
	c5.insert(-a);
	c5.insert(-b);
	c5.insert(c_out);
	clauses.push_back(c5);

	Clause c6; // ¬b ∨ ¬c_in ∨ c_out
	c6.insert(-b);
	c6.insert(-c_in);
	c6.insert(c_out);
	clauses.push_back(c6);

	Clause c7; // ¬c_in ∨ ¬a ∨ c_out
	c7.insert(-c_in);
	c7.insert(-a);
	c7.insert(c_out);
	clauses.push_back(c7);

	Clause c8; // a ∨ ¬c_out
	c8.insert(a);
	c8.insert(-c_out);
	clauses.push_back(c8);

	Clause c9; // b ∨ ¬c_out
	c9.insert(b);
	c9.insert(-c_out);
	clauses.push_back(c9);

	Clause c10; // c_in ∨ ¬c_out
	c10.insert(c_in);
	c10.insert(-c_out);
	clauses.push_back(c10);
	return clauses;

}

std::vector<Clause> Solver::add_half_adder_clauses(int a, int b, int sum, int c_out) {
	std::vector<Clause> clauses;
	// Sum bit clauses
	Clause c1; //  ¬a ∨ ¬b ∨ s
	c1.insert(-a);
	c1.insert(-b);
	c1.insert(sum);
	clauses.push_back(c1);

	Clause c2; //  a ∨ b ∨ ¬s
	c2.insert(a);
	c2.insert(b);
	c2.insert(-sum);
	clauses.push_back(c2);

	// Carry-out bit clauses
	Clause c3; // ¬a ∨ ¬b ∨ c_out
	c3.insert(-a);
	c3.insert(-b);
	c3.insert(-c_out);
	clauses.push_back(c3);

	Clause c4; // a ∨ ¬c_out
	c4.insert(a);
	c4.insert(-c_out);
	clauses.push_back(c4);

	Clause c5; // b ∨ ¬c_out
	c5.insert(b);
	c5.insert(-c_out);
	clauses.push_back(c5); 
	return clauses;
}


/******************  Reading the CNF ******************************/
#pragma region readCNF
void skipLine(ifstream& in) {
	for (;;) {
		//if (in.get() == EOF || in.get() == '\0') return;
		if (in.get() == '\n') { return; }
	}
}

static void skipWhitespace(ifstream& in, char&c) {
	c = in.get();
	while ((c >= 9 && c <= 13) || c == 32)
		c = in.get();
}

static int parseInt(ifstream& in) {
	int     val = 0;
	bool    neg = false;
	char c;
	skipWhitespace(in, c);
	if (c == '-') neg = true, c = in.get();
	if (c < '0' || c > '9') cout << c, Abort("Unexpected char in input", 1);
	while (c >= '0' && c <= '9')
		val = val * 10 + (c - '0'),
		c = in.get();
	return neg ? -val : val;
}

void Solver::read_cnf(ifstream& in) {
	int i;
	unsigned int vars, clauses, unary = 0;
	set<Lit> s;
	Clause c;


	while (in.peek() == 'c') skipLine(in);

	if (!match(in, "p cnf")) Abort("Expecting `p cnf' in the beginning of the input file", 1);
	in >> vars; // since vars is int, it reads int from the stream.
	in >> clauses;
	if (!vars || !clauses) Abort("Expecting non-zero variables and clauses", 1);
	cout << "vars: " << vars << " clauses: " << clauses << endl;
	cnf.reserve(clauses);

	set_nvars(vars);
	set_nclauses(clauses);
	initialize();

	while (in.good() && in.peek() != EOF) {
		i = parseInt(in);
		if (i == 0) {
			c.cl().resize(s.size());
			copy(s.begin(), s.end(), c.cl().begin());
			switch (c.size()) {
			case 0: {
				stringstream num;  // this allows to convert int to string
				num << cnf_size() + 1; // converting int to string.
				Abort("Empty clause not allowed in input formula (clause " + num.str() + ")", 1); // concatenating strings
			}
			case 1: {
				Lit l = c.cl()[0];
				// checking if we have conflicting unaries. Sufficiently rare to check it here rather than 
				// add a check in BCP. 
				if (state[l2v(l)] != VarState::V_UNASSIGNED)
					if (Neg(l) != (state[l2v(l)] == VarState::V_FALSE)) {
						S.print_stats();
						Abort("UNSAT (conflicting unaries for var " + to_string(l2v(l)) +")", 0);
					}
				assert_lit(l);
				add_unary_clause(l);
				break; // unary clause. Note we do not add it as a clause. 
			}
			default: add_clause(c, 0, 1);
			}
			c.reset();
			s.clear();
			continue;
		}
		if (Abs(i) > vars) Abort("Literal index larger than declared on the first line", 1);
		if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) bumpVarScore(abs(i));
		i = v2l(i);		
		if (ValDecHeuristic == VAL_DEC_HEURISTIC::LITSCORE) bumpLitScore(i);
		s.insert(i);
	}	
	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) reset_iterators();
	cout << "Read " << cnf_size() << " clauses in " << cpuTime() - begin_time << " secs." << endl << "Solving..." << endl;
}

#pragma endregion readCNF

void Solver::read_pb(std::ifstream& in) {
	int vars, constraints;
	in >> vars >> constraints;
	set_nvars(vars);
	initialize();
	pbConstraints.clear();
	rhs_values.clear();
	var_to_pb_constraints.clear();
	var_occurrence_count.clear();

	std::cout << "constraints size = " << constraints << "\n";
	in.ignore(std::numeric_limits<std::streamsize>::max(), '\n');  // Move to the next line

	for (int i = 0; i < constraints; ++i) {
		std::vector<std::pair<int, int>> terms;
		std::string constraint_line;
		int rhs;
		std::string op;

		std::cout << "Reading Constraint " << (i + 1) << "\n";

		// Read full constraint line
		if (!std::getline(in, constraint_line) || constraint_line.empty()) {
			std::cerr << "Error: Failed to read constraint " << (i + 1) << "\n";
			continue;  // Skip and move to the next constraint
		}

		std::cout << "Full Constraint Line: " << constraint_line << "\n";

		std::istringstream constraint_stream(constraint_line);
		std::vector<std::string> tokens;
		std::string token;

		// Tokenize the entire line
		while (constraint_stream >> token) {
			tokens.push_back(token);
		}

		// Ensure we have enough tokens
		if (tokens.size() < 3) {
			std::cerr << "Error: Malformed constraint format in line: " << constraint_line << "\n";
			continue;  // Skip this constraint
		}

		// Extract operator (second-last token) and RHS (last token)
		op = tokens[tokens.size() - 2];
		rhs = std::stoi(tokens[tokens.size() - 1]);

		std::cout << "Read operator '" << op << "' and RHS " << rhs << "\n";

		// Parse coefficients and variables
		for (size_t j = 0; j < tokens.size() - 2; j += 2) {
			int coeff = std::stoi(tokens[j]);
			int var = std::stoi(tokens[j + 1]);
			terms.emplace_back(coeff, var);
			std::cout << "  coeff = " << coeff << " var = " << var << "\n";

			var_to_pb_constraints[var].push_back(i);
			var_occurrence_count[var]++;
		}

		std::cout << "Constraint " << (i + 1) << ": ";
		for (const auto& term : terms) {
			std::cout << term.first << "x" << term.second << " ";
		}
		std::cout << " " << op << " " << rhs << "\n";

		pbConstraints.push_back(terms);
		rhs_values[i] = rhs;
		lhs_values[i] = 0;
		bool flag_flip = false;
		if (op == ">" || op == ">=")
			flag_flip = true;
		std::cout << "RHS for constraint " << (i +1 )<< " " << rhs_values[i] << "\n";
		S.normalizePBConstraint(pbConstraints[i],i , rhs_values[i], flag_flip);
		

		for (const auto& term : pbConstraints[i]) {
			std::cout << "coeff: " << term.first << std::endl;
			std::cout << "var: " << term.second << std::endl;
			std::cout << "lit: " << v2l(term.second) << std::endl;

		}
	}

	std::cout << "Successfully loaded " << constraints << " PB constraints.\n";
}

//debugging 
void Solver::print_variable_count(int var) {
	if (var_occurrence_count.find(var) == var_occurrence_count.end()) {
		std::cout << "Variable x" << var << " does not appear in any constraint.\n";
		return;
	}

	std::cout << "Variable x" << var << " appears " << var_occurrence_count[var] << " times across all constraints.\n";
}
/******************  Solving ******************************/
#pragma region solving
void Solver::reset() { // invoked initially + every restart
	dl = 0;
	max_dl = 0;
	conflicting_clause_idx = -1;	
	separators.push_back(0); // we want separators[1] to match dl=1. separators[0] is not used.
	conflicts_at_dl.push_back(0);
}


inline void Solver::reset_iterators(double where) {
	m_Score2Vars_it = (where == 0) ? m_Score2Vars.begin() : m_Score2Vars.lower_bound(where);
	Assert(m_Score2Vars_it != m_Score2Vars.end());
	m_VarsSameScore_it = m_Score2Vars_it->second.begin();
	m_should_reset_iterators = false;
}

void Solver::initialize() {	
	
	state.resize(nvars + 1, VarState::V_UNASSIGNED);
	prev_state.resize(nvars + 1, VarState::V_FALSE); // we set initial assignment with phase-saving to false. 
	antecedent.resize(nvars + 1, -1);	
	marked.resize(nvars+1);
	dlevel.resize(nvars+1);
	
	nlits = 2 * nvars;
	watches.resize(nlits + 1);
	LitScore.resize(nlits + 1);
	//initialize scores 	
	m_activity.resize(nvars + 1);	
	m_curr_activity = 0.0f;
	for (unsigned int v = 0; v <= nvars; ++v) {			
		m_activity[v] = 0;		
	}
	reset();
}

// New method: Evaluates the LHS of a PB Constraint dynamically

//bool Solver::propagatePBConstraints(std::vector<std::pair<int, int>>& pb_constraint) {
//	bool changed = true;
//
//	// 🔹 Compute remaining slack
//	int remainingSlack = rhs - LHS;
//	std::cout << "The value of remainingSlack is: " << remainingSlack << std::endl;
//
//	// 🔹 Step 1: Check for immediate conflict
//	if (remainingSlack < 0) {
//		std::cout << "Conflict detected! Handling conflict...\n";
//		handleConflict(pb_constraint);
//		return false;  // Stop propagation if conflict is detected
//	}
//
//	// 🔹 Step 2: Iterate through the constraint and propagate values
//	for (const auto& term : pb_constraint) {
//		int var = term.second;
//		int coeff = term.first;
//		int lit = v2l(var);
//		// 🔹 Step 3: Assign variable based on slack condition
//		if (get_state_pb(lit) == VarState::V_UNASSIGNED) {
//			if (coeff > remainingSlack) {
//				if (Neg(lit)) {
//					// 🔥 If coefficient is greater than remaining slack, force FALSE assignment
//					set_state_pb(lit, VarState::V_TRUE);
//					std::cout << "Forced Assignment: x" << (var) << " = TRUE (coeff " << coeff << " > remainingSlack " << remainingSlack << ")\n";
//				}
//				else {
//					set_state_pb(lit, VarState::V_FALSE);
//					std::cout << "Forced Assignment: x" << (var) << " = FALSE (coeff " << coeff << " > remainingSlack " << remainingSlack << ")\n";
//				}
//				assigned_num += 1;
//				std::cout << "assigned num " << assigned_num << "\n";
//				std::cout << "nvar " << nvars << "\n";
//			}
//			std::cout << "Updated LHS: " << LHS << ", remainingSlack: " << remainingSlack << "\n";
//		}
//
//
//	}
//	return changed;
//}

//std::vector<int> Solver::findConflictSubset(const std::vector<std::pair<int, int>>& constraint) {
//	std::vector<std::pair<int, int>> sortedTerms = constraint;
//	std::vector<int> conflictSubset;
//
//	// 🔹 Sort terms by coefficient (descending)
//	std::sort(sortedTerms.begin(), sortedTerms.end(),
//		[](const std::pair<int, int>& a, const std::pair<int, int>& b) {
//			return a.first > b.first;
//		});
//
//	int sum = 0;
//	for (const auto& term : sortedTerms) {
//		int var = term.second;
//		int coeff = term.first;
//		int lit = v2l(var);
//		if ((Neg(lit) && get_state_pb(lit) == VarState::V_FALSE) ||
//			(!Neg(lit) && get_state_pb(lit) == VarState::V_TRUE)) {  // Consider only assigned TRUE variables
//			cout << "conflict_var = " << var << endl;
//			conflictSubset.push_back(lit);
//			sum += coeff;
//			if (sum > rhs) {  // 🔥 Stop when sum exceeds b
//				break;
//			}
//		}
//	}
//
//	return conflictSubset;
//}

int getCoefficient(const std::vector<std::pair<int, int>>& constraint, int var) {
	for (const auto& term : constraint) {
		if (term.second == var) {
			return term.first;  // Return coefficient if variable matches
		}
	}
	return 0; // Return 0 if the variable is not found
}
//void Solver::handleConflict(const std::vector<std::pair<int, int>>& constraint) {
//	std::vector<int> conflictSubset = findConflictSubset(constraint);
//
//	if (conflictSubset.empty()) {
//		std::cout << "ERROR: No conflict subset found, but LHS exceeded b!\n";
//		return;
//	}
//
//	Clause conflictClause;
//	for (int lit : conflictSubset) {
//		cout << "conflict_clause = " << negate(lit) << endl;
//		conflictClause.insert(negate(lit));  // 🔥 Negate literals in conflict set
//	}
//
//	if (conflictClause.size() == 1) {
//		Lit clause_lit = conflictClause.lit(0);
//		Lit lit = negate(clause_lit);
//		std::cout << "Unary Conflict Detected! Asserting: " << lit << std::endl;
//		assert_lit(clause_lit);
//		add_unary_clause(clause_lit); 
//		int var = l2v(lit);
//		int coeff;
//		if (Neg(lit))
//		    coeff = getCoefficient(constraint, -var);
//		else
//		    coeff = getCoefficient(constraint, var);
//		if (Neg(clause_lit)) {
//				if (get_state(var) == VarState::V_FALSE)
//				{
//					set_state_pb(var, VarState::V_TRUE);
//					std::cout << "Assignment: x" << (var) << " = False \n";
//					LHS -= coeff;
//				}
//				else
//				{
//					set_state_pb(var, VarState::V_FALSE);
//					std::cout << "Assignment: x" << (var) << " = True \n";
//					LHS += coeff;
//				}
//			}
//			else {
//				if (get_state(var) == VarState::V_FALSE)
//				{
//					set_state_pb(var, VarState::V_FALSE);
//					std::cout << "Assignment: x" << (var) << " = False \n";
//					LHS += coeff;
//				}
//				else
//				{
//					set_state_pb(var, VarState::V_TRUE);
//					std::cout << "Assignment: x" << (var) << " = True \n";
//					LHS -= coeff;
//				}
//			}
//			std::cout << "LHS = " << LHS << "\n";
//			
//	}
//	else {
//		add_clause(conflictClause, 0, 1);
//		// 🔹 Step 3: Call SAT solver to get a new assignment
//		SolverState sat_result = _solve();
//
//		if (sat_result == SolverState::SAT) {
//			std::cout << "SAT.\n";
//			applySATSolution();  // ✅ Apply the new SAT solution
//		}
//		else {
//			std::cerr << "No valid assignment found. UNSAT.\n";
//		}
//	}
//
//
//	
//}


//void Solver::applySATSolution() {
//	std::cout << "Applying new SAT solution to PB solver...\n";
//
//	for (unsigned int i = 1; i <= nvars; ++i) {
//		VarState sat_value = get_state(i);  // Get SAT solver's assignment
//
//		// 🔹 Apply SAT solver's assignment to PB solver
//		set_state(i, sat_value);
//		std::cout << "Variable x" << i << " assigned to " << (sat_value == VarState::V_TRUE ? "TRUE" : "FALSE") << std::endl;
//	}
//
//	std::cout << "New SAT solution applied. Continuing PB solving...\n";
//}

inline void Solver::assert_lit(Lit l) {
	trail.push_back(l);
	int var = l2v(l);
	if (Neg(l)) prev_state[var] = state[var] = VarState::V_FALSE; else prev_state[var] = state[var] = VarState::V_TRUE;
	if (state[var] == VarState::V_FALSE) std::cout <<  "false\n";
	dlevel[var] = dl;
	++num_assignments;
	if (verbose_now()) cout << l2rl(l) <<  " @ " << dl << endl;
}

void Solver::m_rescaleScores(double& new_score) {
	if (verbose_now()) cout << "Rescale" << endl;
	new_score /= Rescale_threshold;
	for (unsigned int i = 1; i <= nvars; i++)
		m_activity[i] /= Rescale_threshold;
	m_var_inc /= Rescale_threshold;
	// rebuilding the scaled-down m_Score2Vars.
	map<double, unordered_set<Var>, greater<double>> tmp_map;
	double prev_score = 0.0f;
	for (auto m : m_Score2Vars) {
		double scaled_score = m.first / Rescale_threshold;
		if (scaled_score == prev_score) // This can happen due to rounding
			tmp_map[scaled_score].insert(m_Score2Vars[m.first].begin(), m_Score2Vars[m.first].end());
		else
			tmp_map[scaled_score] = m_Score2Vars[m.first];
		prev_score = scaled_score;
	}
	tmp_map.swap(m_Score2Vars);
}

void Solver::bumpVarScore(int var_idx) {
	double new_score;
	double score = m_activity[var_idx];		

	if (score > 0) {
		Assert(m_Score2Vars.find(score) != m_Score2Vars.end());
		m_Score2Vars[score].erase(var_idx);
		if (m_Score2Vars[score].size() == 0) m_Score2Vars.erase(score);
	}
	new_score = score + m_var_inc;
	m_activity[var_idx] = new_score;

	// Rescaling, to avoid overflows; 
	if (new_score > Rescale_threshold) {
		m_rescaleScores(new_score);
	}

	if (m_Score2Vars.find(new_score) != m_Score2Vars.end())
		m_Score2Vars[new_score].insert(var_idx);
	else
		m_Score2Vars[new_score] = unordered_set<int>({ var_idx });
}

void Solver::bumpLitScore(int lit_idx) {
	LitScore[lit_idx]++;
}

void Solver::add_clause(Clause& c, int l, int r) {	
	Assert(c.size() > 1) ;
	c.lw_set(l);
	c.rw_set(r);
	int loc = static_cast<int>(cnf.size());  // the first is in location 0 in cnf	
	int size = c.size();
	
	watches[c.lit(l)].push_back(loc); 
	watches[c.lit(r)].push_back(loc);
	cnf.push_back(c);
}

void Solver::add_unary_clause(Lit l) {	
	unaries.push_back(l);
}

int Solver :: getVal(Var v) {
	switch (ValDecHeuristic) {
	case VAL_DEC_HEURISTIC::PHASESAVING: {
		VarState saved_phase = prev_state[v];		
		switch (saved_phase) {
		case VarState::V_FALSE:	return v2l(-v);
		case VarState::V_TRUE: return v2l(v);
		default: Assert(0);
		}
	}
	case VAL_DEC_HEURISTIC::LITSCORE:
	{
		int litp = v2l(v), litn = v2l(-v);
		int pScore = LitScore[litp], nScore = LitScore[litn];
		return pScore > nScore ? litp : litn;
	}
	default: Assert(0);
	}	
	return 0;
}

SolverState Solver::decide(){
	if (verbose_now()) cout << "decide" << endl;
	Lit best_lit = 0;	
	int max_score = 0;
	Var bestVar = 0;
	switch (VarDecHeuristic) {

	case  VAR_DEC_HEURISTIC::MINISAT: {
		// m_Score2Vars_r_it and m_VarsSameScore_it are fields. 
		// When we get here they are the location where we need to start looking. 		
		if (m_should_reset_iterators) reset_iterators(m_curr_activity);
		Var v = 0;
		int cnt = 0;
		if (m_Score2Vars_it == m_Score2Vars.end()) break;
		while (true) { // scores from high to low
			while (m_VarsSameScore_it != m_Score2Vars_it->second.end()) {
				v = *m_VarsSameScore_it;
				++m_VarsSameScore_it;
				++cnt;
				if (state[v] == VarState::V_UNASSIGNED) { // found a var to assign
					m_curr_activity = m_Score2Vars_it->first;
					assert(m_curr_activity == m_activity[v]);
					best_lit = getVal(v);					
					goto Apply_decision;
				}
			}
			++m_Score2Vars_it;
			if (m_Score2Vars_it == m_Score2Vars.end()) break;
			m_VarsSameScore_it = m_Score2Vars_it->second.begin();
		}
		break;
	}
	default: Assert(0);
	}	
		
	assert(!best_lit);
	S.print_state(Assignment_file);
	return SolverState::SAT;


Apply_decision:	
	dl++; // increase decision level
	if (dl > max_dl) {
		max_dl = dl;
		separators.push_back(trail.size());
		conflicts_at_dl.push_back(num_learned);
	}
	else {
		separators[dl] = trail.size();
		conflicts_at_dl[dl] = num_learned;
	}
	
	assert_lit(best_lit);
	++num_decisions;	
	return SolverState::UNDEF;
}

inline ClauseState Clause::next_not_false(bool is_left_watch, Lit other_watch, bool binary, int& loc) {  
	if (verbose_now()) cout << "next_not_false" << endl;
	
	if (!binary)
		for (vector<int>::iterator it = c.begin(); it != c.end(); ++it) {
			LitState LitState = S.lit_state(*it);
			if (LitState != LitState::L_UNSAT && *it != other_watch) { // found another watch_lit
				loc = distance(c.begin(), it);
				if (is_left_watch) lw = loc;    // if literal was the left one 
				else rw = loc;				
				return ClauseState::C_UNDEF;
			}
		}
	switch (S.lit_state(other_watch)) {
	case LitState::L_UNSAT: // conflict
		if (verbose_now()) { print_real_lits(); cout << " is conflicting" << endl; }
		return ClauseState::C_UNSAT;
	case LitState::L_UNASSIGNED: return ClauseState::C_UNIT; // unit clause. Should assert the other watch_lit.	
	case LitState::L_SAT: return ClauseState::C_SAT; // other literal is satisfied. 
	default: Assert(0); return ClauseState::C_UNDEF; // just to supress warning. 
	}
}

void Solver::test() { // tests that each clause is watched twice. 	
	for (unsigned int idx = 0; idx < cnf.size(); ++idx) {
		Clause c = cnf[idx];
		bool found = false;
		for (int zo = 0; zo <= 1; ++zo) {
			for (vector<int>::iterator it = watches[c.cl()[zo]].begin(); !found && it != watches[c.cl()[zo]].end(); ++it) {				
				if (*it == idx) {
					found = true;
					break;
				}
			}
		}
		if (!found) {
			cout << "idx = " << idx << endl;
			c.print();
			cout << endl;
			cout << c.size();
		}
		Assert(found);
	}
}

SolverState Solver::BCP() {
	if (verbose_now()) cout << "BCP" << endl;
	if (verbose_now()) cout << "qhead = " << qhead << " trail-size = " << trail.size() << endl;
	while (qhead < trail.size()) { 
		Lit NegatedLit = negate(trail[qhead++]);
		Assert(lit_state(NegatedLit) == LitState::L_UNSAT);
		if (verbose_now()) cout << "propagating " << l2rl(negate(NegatedLit)) << endl;
		vector<int> new_watch_list; // The original watch list minus those clauses that changed a watch. The order is maintained. 
		int new_watch_list_idx = watches[NegatedLit].size() - 1; // Since we are traversing the watch_list backwards, this index goes down.
		new_watch_list.resize(watches[NegatedLit].size());
		for (vector<int>::reverse_iterator it = watches[NegatedLit].rbegin(); it != watches[NegatedLit].rend() && conflicting_clause_idx < 0; ++it) {
			Clause& c = cnf[*it];
			Lit l_watch = c.get_lw_lit(), 
				r_watch = c.get_rw_lit();			
			bool binary = c.size() == 2;
			bool is_left_watch = (l_watch == NegatedLit);
			Lit other_watch = is_left_watch? r_watch: l_watch;
			int NewWatchLocation;
			ClauseState res = c.next_not_false(is_left_watch, other_watch, binary, NewWatchLocation);
			if (res != ClauseState::C_UNDEF) new_watch_list[new_watch_list_idx--] = *it; //in all cases but the move-watch_lit case we leave watch_lit where it is
			switch (res) {
			case ClauseState::C_UNSAT: { // conflict				
				if (verbose_now()) print_state();
				if (dl == 0) return SolverState::UNSAT;				
				conflicting_clause_idx = *it;  // this will also break the loop
				 int dist = distance(it, watches[NegatedLit].rend()) - 1; // # of entries in watches[NegatedLit] that were not yet processed when we hit this conflict. 
				// Copying the remaining watched clauses:
				for (int i = dist - 1; i >= 0; i--) {
					new_watch_list[new_watch_list_idx--] = watches[NegatedLit][i];
				}
				if (verbose_now()) cout << "conflict" << endl;
				break;
			}
			case ClauseState::C_SAT: 
				if (verbose_now()) cout << "clause is sat" << endl;
				break; // nothing to do when clause has a satisfied literal.
			case ClauseState::C_UNIT: { // new implication				
				if (verbose_now()) cout << "propagating: ";
				assert_lit(other_watch);
				antecedent[l2v(other_watch)] = *it;
				if (verbose_now()) cout << "new implication <- " << l2rl(other_watch) << endl;
				break;
			}
			default: // replacing watch_lit
				Assert(NewWatchLocation < static_cast<int>(c.size()));
				int new_lit = c.lit(NewWatchLocation);
				watches[new_lit].push_back(*it);
				if (verbose_now()) { c.print_real_lits(); cout << " now watched by " << l2rl(new_lit) << endl;}
			}
		}
		// resetting the list of clauses watched by this literal.
		watches[NegatedLit].clear();
		new_watch_list_idx++; // just because of the redundant '--' at the end. 		
		watches[NegatedLit].insert(watches[NegatedLit].begin(), new_watch_list.begin() + new_watch_list_idx, new_watch_list.end());

		//print_watches();
		if (conflicting_clause_idx >= 0) return SolverState::CONFLICT;
		new_watch_list.clear();
	}
	return SolverState::UNDEF;
}


/*******************************************************************************************************************
name: analyze
input:	1) conflicting clause
		2) dlevel
		3) marked
		
assumes: 1) no clause should have the same literal twice. To guarantee this we read through a set in read_cnf. 
            Wihtout this assumption it may loop forever because we may remove only one copy of the pivot.

This is Alg. 1 from "HaifaSat: a SAT solver based on an Abstraction/Refinement model" 
********************************************************************************************************************/

int Solver::analyze(const Clause conflicting) {
	if (verbose_now()) cout << "analyze" << endl;
	Clause	current_clause = conflicting, 
			new_clause;
	int resolve_num = 0,
		bktrk = 0, 
		watch_lit = 0, // points to what literal in the learnt clause should be watched, other than the asserting one
		antecedents_idx = 0;

	Lit u;
	Var v;
	trail_t::reverse_iterator t_it = trail.rbegin();
	do {
		for (clause_it it = current_clause.cl().begin(); it != current_clause.cl().end(); ++it) {
			Lit lit = *it;
			v = l2v(lit);
			if (!marked[v]) {
				marked[v] = true;
				if (dlevel[v] == dl) ++resolve_num;
				else { // literals from previos decision levels (roots) are entered to the learned clause.
					new_clause.insert(lit);
					if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) bumpVarScore(v);
					if (ValDecHeuristic == VAL_DEC_HEURISTIC::LITSCORE) bumpLitScore(lit);
					int c_dl = dlevel[v];
					if (c_dl > bktrk) {
						bktrk = c_dl;
						watch_lit = new_clause.size() - 1;
					}
				}
			}
		} 
		
		while (t_it != trail.rend()) {
			u = *t_it;
			v = l2v(u);
			++t_it;
			if (marked[v]) break;
		}
		marked[v] = false;
		--resolve_num;
		if(!resolve_num) continue; 
		int ant = antecedent[v];		
		current_clause = cnf[ant]; 
		current_clause.cl().erase(find(current_clause.cl().begin(), current_clause.cl().end(), u));	
	}	while (resolve_num > 0);
	for (clause_it it = new_clause.cl().begin(); it != new_clause.cl().end(); ++it) 
		marked[l2v(*it)] = false;
	Lit Negated_u = negate(u);
	new_clause.cl().push_back(Negated_u);		
	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) 
		m_var_inc *= 1 / var_decay; // increasing importance of participating variables.
	
	++num_learned;
	asserted_lit = Negated_u;
	if (new_clause.size() == 1) { // unary clause	
		add_unary_clause(Negated_u);
	}
	else {
		add_clause(new_clause, watch_lit, new_clause.size() - 1);
	}
	

	if (verbose_now()) {	
		cout << "Learned clause #" << cnf_size() + unaries.size() << ". "; 
		new_clause.print_real_lits(); 
		cout << endl;
		cout << " learnt clauses:  " << num_learned;				
		cout << " Backtracking to level " << bktrk << endl;
	}

	if (verbose >= 1 && !(num_learned % 1000)) {
		cout << "Learned: "<< num_learned <<" clauses" << endl;		
	}	
	return bktrk; 
}

void Solver::backtrack(int k) {
	if (verbose_now()) cout << "backtrack" << endl;
	// local restart means that we restart if the number of conflicts learned in this 
	// decision level has passed the threshold. 
	if (k > 0 && (num_learned - conflicts_at_dl[k] > restart_threshold)) {	// "local restart"	
		restart(); 		
		return;
	}
	static int counter = 0;
		
	for (trail_t::iterator it = trail.begin() + separators[k+1]; it != trail.end(); ++it) { // erasing from k+1
		Var v = l2v(*it);
		if (dlevel[v]) { // we need the condition because of learnt unary clauses. In that case we enforce an assignment with dlevel = 0.
			state[v] = VarState::V_UNASSIGNED;
			if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) m_curr_activity = max(m_curr_activity, m_activity[v]);
		}
	}
	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) m_should_reset_iterators = true;
	if (verbose_now()) print_state();
	trail.erase(trail.begin() + separators[k+1], trail.end());
	qhead = trail.size();
	dl = k;	
	assert_lit(asserted_lit);
	antecedent[l2v(asserted_lit)] = cnf.size() - 1;
	conflicting_clause_idx = -1;
}

void Solver::validate_assignment() {
	for (unsigned int i = 1; i <= nvars; ++i) if (state[i] == VarState::V_UNASSIGNED) {
		cout << "Unassigned var: " + to_string(i) << endl; // This is supposed to happen only if the variable does not appear in any clause
	}
	for (vector<Clause>::iterator it = cnf.begin(); it != cnf.end(); ++it) {
		int found = 0;
		for(clause_it it_c = it->cl().begin(); it_c != it->cl().end() && !found; ++it_c) 
			if (lit_state(*it_c) == LitState::L_SAT) found = 1;
		if (!found) {
			cout << "fail on clause: "; 
			it->print();
			cout << endl;
			for (clause_it it_c = it->cl().begin(); it_c != it->cl().end() && !found; ++it_c)
				cout << *it_c << " (" << (int) lit_state(*it_c) << ") ";
			cout << endl;
			Abort("Assignment validation failed", 3);
		}
	}
	for (vector<Lit>::iterator it = unaries.begin(); it != unaries.end(); ++it) {
		if (lit_state(*it) != LitState::L_SAT) 
			Abort("Assignment validation failed (unaries)", 3);
	}
	cout << "Assignment validated" << endl;
}

void Solver::restart() {	
	if (verbose_now()) cout << "restart" << endl;
	restart_threshold = static_cast<int>(restart_threshold * restart_multiplier);
	if (restart_threshold > restart_upper) {
		restart_threshold = restart_lower;
		restart_upper = static_cast<int>(restart_upper  * restart_multiplier);
		if (verbose >= 1) cout << "new restart upper bound = " << restart_upper << endl;
	}
	if (verbose >=1) cout << "restart: new threshold = " << restart_threshold << endl;
	++num_restarts;
	for (unsigned int i = 1; i <= nvars; ++i) 
		if (dlevel[i] > 0) {
			state[i] = VarState::V_UNASSIGNED;
			dlevel[i] = 0;
		}	
	trail.clear();
	qhead = 0;
	separators.clear(); 
	conflicts_at_dl.clear(); 
	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) {
		m_curr_activity = 0; // The activity does not really become 0. When it is reset in decide() it becomes the largets activity. 
		m_should_reset_iterators = true;
	}
	reset();
}

void Solver::solve() { 
	SolverState res = _solve(); 	
	Assert(res == SolverState::SAT || res == SolverState::UNSAT || res == SolverState::TIMEOUT);
	S.print_stats();
	switch (res) {
	case SolverState::SAT: {
		S.validate_assignment();
		string str = "solution in ",
			str1 = Assignment_file;
		cout << str + str1 << endl;
		cout << "SAT" << endl;
		break;
	}
	case SolverState::UNSAT: 
		cout << "UNSAT" << endl;
		break;
	case SolverState::TIMEOUT: 
		cout << "TIMEOUT" << endl;
		return;
	}	
	return;
}

SolverState Solver::_solve() {
	SolverState res;
	while (true) {
		if (timeout > 0 && cpuTime() - begin_time > timeout) return SolverState::TIMEOUT;
		while (true) {
			res = BCP();
			if (res == SolverState::UNSAT) return res;
			if (res == SolverState::CONFLICT) 
				backtrack(analyze(cnf[conflicting_clause_idx]));
			else break;
		}
		res = decide();
		if (res == SolverState::SAT) return res;
	}
}

void Solver::normalizePBConstraint(std::vector<std::pair<int, int>>& pb_constraint,int& num_constraint, int& rhs, bool bigger) {
	std::vector<std::pair<int, int>> newConstraint;

	// 🔹 Step 1: Flip inequality if RHS is negative
	if (bigger) {
		rhs *= -1;  // Convert RHS to positive
		for (auto& term : pb_constraint) {
			term.first *= -1;  // Multiply coefficients by -1
		}
	}

	// 🔹 Step 2: Convert each term correctly
	for (auto& term : pb_constraint) {
		int coeff = term.first;
		int var = term.second;

		if (coeff < 0) {
			// 🔥 Apply transformation: x_i = 1 - x̅_i
			rhs += (-coeff);  // Adjust RHS by subtracting the negated term
		}
		rhs_values[num_constraint] = rhs;
		newConstraint.push_back({ coeff, var });
	}
	std::cout << "RHS for constraint for "<< (num_constraint+ 1) << " after normalization "<< " " << rhs_values[num_constraint] << "\n";
	pb_constraint = std::move(newConstraint);

}

int Solver::choose_best_variable() {
	int best_var = -1;
	int max_score = -1;

	// Iterate over all variables in constraints
	for (const auto& entry : var_occurrence_count) {
		int var = entry.first;
		int count = entry.second;  // How many constraints this variable appears in
		int total_weight = 0;
		if (get_state_pb(var) != VarState::V_UNASSIGNED)
			continue;
		vector<std::pair<int, int>> pbConstraint;
		// Sum coefficients across constraints
		for (int constraint_idx : var_to_pb_constraints[var]) {
			pbConstraint = pbConstraints[constraint_idx];
			for (const auto& term : pbConstraint) {
				if (term.second == var) {
					total_weight += abs(term.first);  // Coefficient of this variable
					break;
				}
			}
		}

		int score = total_weight * count;  // Weighted score
		if (score > max_score) {
			best_var = var;
			max_score = score;
		}
	}

	return best_var;
}
//bool Solver::propagatePBConstraints(int assigned_var) {
//	for (int constraint_idx : var_to_pb_constraints[assigned_var])
//	{
//		std::cout << "🔍 Propagating in Constraint " << (constraint_idx + 1) << "\n";
//		vector<std::pair<int, int>> pbConstraint = pbConstraints[constraint_idx];
//		int rhs = rhs_values[constraint_idx];
//		int LHS = lhs_values[constraint_idx];
//		// 🔹 Compute remaining slack
//		int remainingSlack = rhs - LHS;
//		// Calculate the new LHS value
//		for (const auto& term : pbConstraints[constraint_idx]) {
//			int coeff = term.first;
//			int var = term.second;
//			bool changed = true;
//
//			// 🔹 Compute remaining slack
//			int remainingSlack = rhs - LHS;
//			std::cout << "The value of remainingSlack is: " << remainingSlack << std::endl;
//
//			// 🔹 Step 1: Check for immediate conflict
//			if (remainingSlack < 0) {
//				std::cout << "Conflict detected! Handling conflict...\n";
//				handleConflict(pb_constraint);
//				return false;  // Stop propagation if conflict is detected
//			}
//
//			// 🔹 Step 2: Iterate through the constraint and propagate values
//			for (const auto& term : pb_constraint) {
//				int var = term.second;
//				int coeff = term.first;
//				int lit = v2l(var);
//				// 🔹 Step 3: Assign variable based on slack condition
//				if (get_state_pb(lit) == VarState::V_UNASSIGNED) {
//					if (coeff > remainingSlack) {
//						if (Neg(lit)) {
//							// 🔥 If coefficient is greater than remaining slack, force FALSE assignment
//							set_state_pb(lit, VarState::V_TRUE);
//							std::cout << "Forced Assignment: x" << (var) << " = TRUE (coeff " << coeff << " > remainingSlack " << remainingSlack << ")\n";
//						}
//						else {
//							set_state_pb(lit, VarState::V_FALSE);
//							std::cout << "Forced Assignment: x" << (var) << " = FALSE (coeff " << coeff << " > remainingSlack " << remainingSlack << ")\n";
//						}
//						assigned_num += 1;
//						std::cout << "assigned num " << assigned_num << "\n";
//						std::cout << "nvar " << nvars << "\n";
//					}
//					std::cout << "Updated LHS: " << LHS << ", remainingSlack: " << remainingSlack << "\n";
//				}
//
//
//			}
//			return changed;
//		}
//
//		}
//	}
//}



void Solver::propagatePBConstraints(int assigned_var, VarState state, bool flip) {
	dl_pb++;
	for (int constraint_idx : var_to_pb_constraints[assigned_var]) {
		int rhs = rhs_values[constraint_idx];
		int& LHS = lhs_values[constraint_idx]; // Reference to update global LHS
		std::cout << "Propagating in Constraint " << (constraint_idx + 1) << "\n";
		// 🔹 Step 1: Update LHS for the assigned variable
		for (auto& term : pbConstraints[constraint_idx]) {
			int coeff = term.first;
			int var = term.second;

			if (var == assigned_var) {
				// Save previous state before assignment
				prev_state[var] = (flip ? VarState::V_UNASSIGNED : state_pb[var]);

				set_state_pb(var, state);
				dlevel_pb[var] = dl_pb;
				trail_pb.push_back(var);

				// 🔹 Adjust LHS based on assignment
				if (coeff < 0) {
					if (state == VarState::V_FALSE) {
						std::cout << "Assignment: x" << var << " = FALSE\n";
						LHS += abs(coeff);
					}
				
				}
				else {
					if (state == VarState::V_TRUE) {
						std::cout << "Assignment: x" << var << " = TRUE\n";
						LHS += abs(coeff);
					}
				
				}

				// Mark assigned variable
				if (assigned_vars.find(var) == assigned_vars.end()) {
					assigned_vars.insert(var);
					assigned_num++;
				}
			}
		}

		// 🔹 Step 2: Compute remaining slack **after updating LHS**
		int remainingSlack = rhs - LHS;
		if (remainingSlack < 0) {
			std::cout << "Conflict detected in Constraint " << (constraint_idx + 1) << "\n";
			backtrack_pb();
			break;
		}

		// 🔹 Step 3: Assign unassigned variables
		for (auto& term : pbConstraints[constraint_idx]) {
			int coeff = term.first;
			int var = term.second;

			if (state_pb[var] == VarState::V_UNASSIGNED && abs(coeff) > remainingSlack) {
				prev_state[var] = state_pb[var];
				dlevel_pb[var] = dl_pb;
				trail_pb.push_back(var);

				// Forced assignment based on remaining slack
				if (coeff < 0) {
					set_state_pb(var, VarState::V_TRUE);
					std::cout << "Forced Assignment: x" << var << " = TRUE (coeff " << coeff << " > remainingSlack " << remainingSlack << ")\n";
				}
				else {
					set_state_pb(var, VarState::V_FALSE);
					std::cout << "Forced Assignment: x" << var << " = FALSE (coeff " << coeff << " > remainingSlack " << remainingSlack << ")\n";
				}

				// Mark assigned variable
				if (assigned_vars.find(var) == assigned_vars.end()) {
					assigned_vars.insert(var);
					assigned_num++;
				}
			}
		}

		std::cout << "Updated LHS = " << LHS << ", RHS = " << rhs << "\n";

		// 🔹 Step 4: Conflict check

	}

}


void Solver::backtrack_pb() {
	std::cout << "Backtracking from decision level " << dl_pb<< "\n";

	if (dl_pb == 0) {
		std::cout << "No more decisions to backtrack.UNSAT.\n";
		return;
	}

	// Undo all assigned variables at the current decision level
	while (!trail_pb.empty()) {
		int var = trail_pb.back();
		trail_pb.pop_back();

		if (var == -1) {  // Decision level marker
			dl_pb--;  // Move to the previous level
			break;
		}

		// Reset the variable only if it was assigned at the current decision level
		if (dlevel_pb[var] == dl_pb) {
				// 🔹 Undo LHS changes for all constraints this variable was in
			prev_state_pb[var] = state_pb[var];
			state_pb[var] = VarState::V_UNASSIGNED;
			dlevel_pb[var] = -1;  // Mark as unassigned
			if (assigned_vars.find(var) != assigned_vars.end()) {
				assigned_vars.erase(var);
				assigned_num--;  // Ensure assigned_num is updated properly
			}

			std::cout << "Unassigning x" << var << "\n";
		}
	}

	if (!trail_pb.empty()) {
		// Flip the last decision variable
		int last_decision_var = trail_pb.back();
		trail_pb.pop_back();
		VarState state;
		for (int constraint_idx : var_to_pb_constraints[last_decision_var]) {
			int coeff = getCoefficient(pbConstraints[constraint_idx], last_decision_var);

			if (coeff < 0) {
				if (prev_state_pb[last_decision_var] == VarState::V_FALSE)
					lhs_values[constraint_idx] -= abs(coeff);  // Undo LHS increment

			}
			else {
				if (prev_state_pb[last_decision_var] == VarState::V_TRUE) {
					lhs_values[constraint_idx] -= abs(coeff);  // Undo LHS increment
				}

			}

			std::cout << "🔄 Undoing LHS update for constraint " << (constraint_idx + 1)
				<< " | New LHS = " << lhs_values[constraint_idx] << "\n";
		}
		std::cout << "Flipping x" << last_decision_var << " to FALSE for backtracking\n";
		if (prev_state_pb[last_decision_var] == VarState::V_TRUE)
			state = VarState::V_FALSE;
		else
			state = VarState::V_TRUE;
		// Restart propagation after flipping the decision
		propagatePBConstraints(last_decision_var,state,true);
	}
}




bool Solver::solvePBConstraints(){
	// 🔹 Step 1: Sort variables by coefficient (descending)
	std::vector<std::pair<int, int>>  pb_constraint;


	std::cout << "The value of nvar is: " << nvars << std::endl;
	assigned_num = 0;
	dl_pb = 0;
	
	std::cout << "The value of nlits is: " << 2*nvars << std::endl;
	state_pb.assign(nvars+1, VarState::V_UNASSIGNED);
	prev_state_pb.assign(nvars + 1, VarState::V_UNASSIGNED);  // Store previous state
	dlevel_pb.assign(nvars + 1, -1);  // Reset decision levels
	while (assigned_num != nvars) {
		int best_var = choose_best_variable();
		std::cout << "the best var is " << best_var << "\n";
		trail_pb.push_back(best_var);
		trail_pb.push_back(-1);
		propagatePBConstraints(best_var, VarState::V_TRUE, false);
		

	}
	for (size_t constraint_idx = 0; constraint_idx < pbConstraints.size(); ++constraint_idx) {

		if (lhs_values[constraint_idx] > rhs_values[constraint_idx]) {
			// 🔥 Step 5: If no assignment worked, it's UNSAT
			std::cout << "No valid assignment found. UNSAT.\n";
			return false;

		}
		std::cout << "Solution found \n";
		return true;  // ✅ Constraint satisfied
	}

	
}

//bool Solver::solvePBConstraints(const std::vector<std::vector<std::pair<int, int>>>& pb_constraints, const std::vector<int>& rhs_values) {
//	// 🔹 Step 1: Sort variables by coefficient (descending)
//	std::vector<std::pair<int, int>>  pb_constraint;
//	pb_constraint = pb_constraints[0];
//	if (pb_constraint.empty()) {
//		std::cerr << "Error: No valid constraints to process!\n";
//		return false;
//	}
//	set_nvars(pb_constraint.size());
//	initialize();
//	std::cout << "The value of nvar is: " << nvars << std::endl;
//	assigned_num = 0;
//
//	std::cout << "The value of nlits is: " << 2 * nvars << std::endl;
//	state_pb.assign(2 * nvars + 1, VarState::V_UNASSIGNED);
//	std::sort(pb_constraint.begin(), pb_constraint.end(),
//		[](const std::pair<int, int>& a, const std::pair<int, int>& b) {
//			return a.first > b.first;  // Sort by largest coefficient first
//		});
//	while (assigned_num != nvars) {
//		for (auto& term : pb_constraint) {
//			if (assigned_num == nvars) break;
//			int coeff = term.first;
//			int var = term.second;
//			int lit = v2l(var);
//			if (lit >= 0 && lit < state_pb.size()) {
//				if (get_state_pb(lit) != VarState::V_UNASSIGNED) continue;
//				if (Neg(lit)) {
//					set_state_pb(lit, VarState::V_FALSE);
//					std::cout << "Assignment: x" << (var) << " = False \n";
//
//				}
//				else
//				{
//					set_state_pb(lit, VarState::V_TRUE);
//					std::cout << "Assignment: x" << (var) << " = True \n";
//
//				}
//				int lhs_p = LHS;
//				set_LHS(lhs_p + coeff);
//				assigned_num += 1;
//				std::cout << "The value of currentLHS is: " << LHS << std::endl;
//			}
//			else {
//				std::cerr << "Error: Variable index out of bounds: " << var << "\n";
//			}
//
//			// 🔹 Step 3: Propagate implications
//			if (!propagatePBConstraints(pb_constraint)) {
//				std::cout << "Conflict occurred after assigning Backtracking...\n";
//
//			}
//
//		}
//
//	}
//	// 🔹 Step 4: Stop if satisfied
//	if (LHS <= rhs) {
//		std::cout << "Solution found: LHS = " << LHS << " <= " << rhs << "\n";
//		return true;  // ✅ Constraint satisfied
//
//	}
//
//	// 🔥 Step 5: If no assignment worked, it's UNSAT
//	std::cout << "No valid assignment found. UNSAT.\n";
//	return false;
//}

//bool Solver::solvePBConstraints(const std::vector<std::vector<std::pair<int, int>>>& pb_constraints, const std::vector<int>& rhs_values) {
//	if (pb_constraints.empty() || rhs_values.empty() || pb_constraints.size() != rhs_values.size()) {
//		std::cerr << "Error: Constraints and RHS values must have the same size!\n";
//		return false;
//	}
//
//	// 🔹 Compute the number of distinct variables
//	int max_var = 0;
//	for (const auto& constraint : pb_constraints) {
//		for (const auto& term : constraint) {
//			max_var = std::max(max_var, term.second);
//		}
//	}
//	set_nvars(max_var);  // Set the correct number of variables
//
//	initialize();
//	std::cout << "Total distinct variables (nvars): " << max_var << "\n";
//	//std::vector<int> global_assignments(max_var + 1, -1); // -1 means unassigned
//
//	bool changed = true;
//	while (changed) {
//		changed = false;
//
//		for (size_t i = 0; i < pb_constraints.size(); ++i) {
//			std::vector<std::pair<int, int>> pb_constraint = pb_constraints[i];
//			int rhs = rhs_values[i];
//
//	/*		normalizePBConstraint(pb_constraint, rhs, false);*/
//
//			std::sort(pb_constraint.begin(), pb_constraint.end(),
//				[](const std::pair<int, int>& a, const std::pair<int, int>& b) {
//					return a.first > b.first;
//				});
//
//			int current_sum = 0;
//			int free_variables = 0;
//			std::vector<int> unassigned_vars;
//
//			for (auto& term : pb_constraint) {
//				int coeff = term.first;
//				int var = term.second;
//
//				if (global_assignments[var] == 1) {
//					current_sum += coeff;
//				}
//				else if (global_assignments[var] == -1) {
//					free_variables += coeff;
//					unassigned_vars.push_back(var);
//				}
//			}
//
//			if (current_sum > rhs) {
//				std::cout << "❌ Constraint " << i + 1 << " UNSAT: Current sum (" << current_sum << ") exceeds RHS (" << rhs << ")\n";
//				return false;
//			}
//
//			if (current_sum + free_variables < rhs) {
//				for (int var : unassigned_vars) {
//					global_assignments[var] = 0;
//					changed = true;
//					std::cout << "🚨 Assigning x" << var << " = False due to constraint " << i + 1 << "\n";
//				}
//			}
//			else if (current_sum >= rhs) {
//				for (int var : unassigned_vars) {
//					global_assignments[var] = 1;
//					changed = true;
//					std::cout << "✅ Assigning x" << var << " = True due to constraint " << i + 1 << "\n";
//				}
//			}
//		}
//	}
//
//	std::cout << "✅ All constraints satisfied!\n";
//	return true;
//}



#pragma endregion solving


/******************  main ******************************/

//int main(int argc, char** argv){
//	begin_time = cpuTime();
//	parse_options(argc, argv);
//	
//	ifstream in (argv[argc - 1]);
//	if (!in.good()) Abort("cannot read input file", 1);	
//	cout << "This is edusat" << endl;
//	S.read_cnf(in);		
//	in.close();
//	S.solve();	
//
//	return 0;
//}

int main() {
	//Solver S;
	//std::vector<std::vector<std::pair<int, int>>> pb_constraint;
	//// 🔥 Example PB Constraint: 4x1 + 3x2 + 2x3 ≤ 5
	//std::vector<std::vector<std::pair<int, int>>> pb_constraints = {
	//   {  {4, 1}, {3, 2}, {2, 3}}, {  {4, 1}, {3, 2}, {3, 4}} // 4x1 + 3x2 + 2x3 ≤ 5 
	//};
	////std::vector<std::pair<int, int>> pb_terms = {
	////	{4, 1},  // Coefficient 4 for variable x1
	////	{3, 2},  // Coefficient 3 for variable x2
	////	{2, 3}   // Coefficient 2 for variable x3
	////};
	//const std::vector<int>& rhs_values = { 5,6 };
	//S.solvePBConstraints(pb_constraints,rhs_values);

	Solver S;
	int best_var;

	std::ifstream file("Input.pb");
	if (!file) {
		std::cerr << "❌ Error: Cannot open input.pb file!\n";
		return 1;
	}

	S.read_pb(file);
	file.close();

	// Print where variable x1 appears
	S.print_variable_count(1);
	S.print_variable_count(2);
	S.print_variable_count(3);
	S.print_variable_count(4);

	//best_var = S.choose_best_variable();
	//std::cout << "the best var is " << best_var << "\n";

	S.solvePBConstraints();
	//if (!pb_constraints.empty()) {
	//	std::vector<std::pair<int, int>>* pb_constraint = &pb_constraints[0];
	//	S.solvePBConstraint(pb_constraints);
	//}

	return 0;
	 
}