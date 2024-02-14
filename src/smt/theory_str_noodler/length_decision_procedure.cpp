#include <queue>
#include <utility>
#include <algorithm>

#include <mata/nfa/strings.hh>

#include "util.h"
#include "aut_assignment.h"
#include "length_decision_procedure.h"
#include <fstream>

#include "util/trace.h"

namespace smt::noodler {

//////////////////////////////////

typedef struct LiteralAggregate_t {
    zstring parent_var;
    zstring literal_name;
} LiteralAggregate;

class VarConstraint
{
private:
	zstring _name;
	std::vector<Concat> _constr_eqs;	// All sides of equations on the opposite side of this variable

	std::vector<LiteralAggregate> _lits; // Literals occuring explicitly and in contained variables

	// std::map<zstring, zstring>& conv;
public:
	lbool is_parsed;
	VarConstraint() : _name(), is_parsed (l_false) {};
	VarConstraint(zstring name) : _name(std::move(name)), is_parsed (l_false) {};
	bool check_side(const Concat& side) {
		return side.size() == 1 && side[0].get_name() == _name;
	}
	bool add(const Predicate& pred) {
		if (check_side(pred.get_left_side())) {
			_constr_eqs.emplace_back(pred.get_right_side());
			return true;
		}
		if (check_side(pred.get_right_side())) {
			_constr_eqs.emplace_back(pred.get_left_side());
			return true;
		}

		return false;
	}

	// !!! Must be called after parse !!!
	const std::vector<LiteralAggregate>& get_lits() const {
		return _lits;
	}

	// TODO: already generate here
	/**
	 * @brief parse var constraint
	 * 
	 * @param pool all var constraints
	 * @param conv conversions for literals
	 * @return bool success
	 */
	bool parse(std::map<zstring,VarConstraint>& pool, std::map<zstring,zstring>& conv) {
		if (is_parsed == l_true) {
			return true;	// Already parsed
		}

		if (is_parsed == l_undef) {
			return false;	// Cycle
		}

		is_parsed = l_undef;	// Currently in parsing

		for (const Concat& side : _constr_eqs) {
			for (const BasicTerm& t : side) {
				if (t.get_type() == BasicTermType::Literal) {
					zstring new_lit_name = util::mk_noodler_var_fresh("lit").get_name();
					conv[new_lit_name] = t.get_name();
					_lits.emplace_back(LiteralAggregate{.parent_var = "", .literal_name = new_lit_name});
				} else if (t.get_type() == BasicTermType::Variable) {

					// If the var is constrained
					if (pool.count(t.get_name())) {
						if (pool[t.get_name()].parse(pool, conv) == false) {
							return false;	// There is a cycle: propagate
						}
						
						for (const LiteralAggregate& l : pool[t.get_name()].get_lits()) {
							_lits.emplace_back(LiteralAggregate{.parent_var = t.get_name(), .literal_name = l.literal_name});
						}
					}
				}
			}
		}

		is_parsed = l_true;
		return true;
	}

	std::string to_string() const {
		std::string ret = "#####\n# VarConstraint: " + _name.encode() + "\n###\n#";
		bool first = true;
		for (const Concat& side : _constr_eqs) {
			if (!first) {
				ret += " =";
			}
			first = false;

			for (const BasicTerm& term : side) {
				// Literals will be displayed just by their name, not by value
				ret += " " + term.to_string();
			}
		}

		ret += "\n###\n# lits:";

		for (const LiteralAggregate& t :_lits) {
			// for explicit: ... lname ...
			// for derived: ... lname (vname) ...
			ret += " " + t.literal_name.encode() + ((t.parent_var == "") ? "" : ("("+t.parent_var.encode()+")"));
		}

		ret += "\n#####\n";
		return ret;
	}
};

static std::ostream& operator<<(std::ostream& os, const VarConstraint& vcon) {
    os << vcon.to_string();
    return os;
}

void add_to_pool(std::map<zstring, VarConstraint>& pool, const Predicate& pred) {
	bool in_pool = false;

	for (const Concat& side : pred.get_params()) {
		if (side.size() == 1 && side[0].get_type() == BasicTermType::Variable) {
			zstring var_name = side[0].get_name();
			if (pool.count(var_name) == 0) {
				pool[var_name] = VarConstraint(var_name);
				pool[var_name].add(pred);
			} else {
				pool[var_name].add(pred);
			}

			in_pool = true;
		}
	}

	if (!in_pool) {
		zstring fresh = util::mk_noodler_var_fresh("f").get_name();
		pool[fresh] = VarConstraint(fresh);
	}
}


///////////////////////////////////

lbool LengthDecisionProcedure::compute_next_solution() {
    std::cerr << "len: compute_next_solution\n===========\n";
    for (const Predicate& pred : this->formula.get_predicates()) {
        std::cerr << pred << std::endl;
    }

    // Check for suitability
    std::vector<zstring> concat_vars = {};	// variables that have appeared in concatenation 
    int len = 0;
    
    for (const Predicate& pred : this->formula.get_predicates()) {
        if (pred.get_type() == PredicateType::NotContains) {
            // TODO: try to resolve not contains
            std::cerr << "len: Cant solve not contains.\n";
            return l_undef;
        }

        for (const Concat& side : pred.get_params()) {
            bool is_concat = side.size() > 1;

            for (const BasicTerm& var : side) {
                // accept literals
                if (init_aut_ass.is_singleton(var)) {
                    continue;
                }

                // Variable is not literal
                if(init_aut_ass.at(var)->num_of_states() <= 1 || init_aut_ass.is_co_finite(var, len)) {
                    assert(var.get_type() == BasicTermType::Variable);
                    if (is_concat) {
                        zstring var_name = var.get_name();  // Name of the variable

                        // Check if variable was in any concatenation
                        for (zstring n : concat_vars) {
                            if (n == var_name) {
                                return l_undef;
                            }
                        }
                        
                        // Note it as a concatenation variable
                        concat_vars.emplace_back(var_name);
                    }
                    continue;
                }

                std::cerr << "len: Not suitable.\n";
                return l_undef;
            }
        }
    }
    // End check for suitability

    std::map<zstring, VarConstraint> pool{};

    for (const Predicate& pred : this->formula.get_predicates()) {
        add_to_pool(pool, pred);
    }

    std::map<zstring, zstring> lit_conversion {};	// Naming literals differently from their value

    for (std::pair<zstring, VarConstraint> it : pool) {
         if (pool[it.first].parse(pool, lit_conversion) == false) {
            // There is a cycle
            return l_undef;	// We cannot solve this formula
        }
    }

    for (std::pair<zstring, VarConstraint> it : pool) {
        std::cerr << it.second << std::endl;
    }

    std::cerr << "\n\nConversions:\n+--------\n";
    for (const std::pair<const zstring, zstring>& conv : lit_conversion) {
        std::cerr << "| " + conv.first.encode() + " : \"" + conv.second.encode() << "\"\n";
    }
    std::cerr << "+--------\n";

    return l_undef;
}

LenNode LengthDecisionProcedure::get_lengths() {
    /**
     * TODO
     */
    throw std::runtime_error("unimplemented");
}

void LengthDecisionProcedure::init_computation() {
    std::cout << "here.\n";
    STRACE("str", tout << "len: Initializing computation..." << std::endl);
}

lbool LengthDecisionProcedure::preprocess(PreprocessType opt, const BasicTermEqiv &len_eq_vars) {
    
    FormulaPreprocessor prep_handler(this->formula, this->init_aut_ass, this->init_length_sensitive_vars, m_params);

    STRACE("str", tout << "len: Preprocessing..." << std::endl);

    // std::ofstream out("len_dec_proc.txt");

    // out << "preprocess\n===========\n";
    // out << "Predicates:\n";
    // for (const Predicate& p : this->formula.get_predicates()) {
    //     out << p << '\n';
    // }

    // out << "\npreprocessing...\n\n";

    prep_handler.reduce_diseqalities();
    // out << "Reduce disequalities:\n-------\n";
    // for (const auto& p : prep_handler.get_formula().get_predicates()) {
    //     out << "  " << p.second << '\n';
    // }
    // out << "-------\n\n";

    prep_handler.underapprox_languages();

    prep_handler.propagate_eps();
    // out << "Propagate epsilon:\n-------\n";
    // for (const auto& p : prep_handler.get_formula().get_predicates()) {
    //     out << "  " << p.second << '\n';
    // }
    // out << "-------\n\n";

    prep_handler.propagate_variables();
    // out << "Propagate variables:\n-------\n";
    // for (const auto& p : prep_handler.get_formula().get_predicates()) {
    //     out << "  " << p.second << '\n';
    // }
    // out << "-------\n\n";

    prep_handler.generate_identities();
    // out << "Generate identities:\n-------\n";
    // for (const auto& p : prep_handler.get_formula().get_predicates()) {
    //     out << "  " << p.second << '\n';
    // }
    // out << "-------\n\n";

    prep_handler.propagate_variables();
    // out << "Propagate variables:\n-------\n";
    // for (const auto& p : prep_handler.get_formula().get_predicates()) {
    //     out << "  " << p.second << '\n';
    // }
    // out << "-------\n\n";


    // prep_handler = FormulaPreprocessor(this->formula, this->init_aut_ass, this->init_length_sensitive_vars, m_params);

    prep_handler.remove_trivial();
    

    // out.close();

    
    // Refresh the instance
    this->formula = prep_handler.get_modified_formula();
    this->init_aut_ass = prep_handler.get_aut_assignment();
    this->init_length_sensitive_vars = prep_handler.get_len_variables();
    this->preprocessing_len_formula = prep_handler.get_len_formula();

    if(this->formula.get_predicates().size() > 0) {
        this->init_aut_ass.reduce(); // reduce all automata in the automata assignment
    }

    if(prep_handler.contains_unsat_eqs_or_diseqs()) {
        return l_false;
    }

    if (!this->init_aut_ass.is_sat()) {
        // some automaton in the assignment is empty => we won't find solution
        return l_false;
    }
    
    if (this->formula.get_predicates().empty()) {
        // preprocessing solved all (dis)equations => we set the solution (for lengths check)
        // TODO ----v
        // this->solution = SolvingState(this->init_aut_ass, {}, {}, {}, this->init_length_sensitive_vars, {});
        return l_true;
    }

    
    
    return l_undef;
}

bool LengthDecisionProcedure::is_suitable(const Formula &form, const AutAssignment& init_aut_ass) {
    // std::vector<zstring> concat_vars = {};	// variables that have appeared in concatenation 
    int len = 0;

    for (const Predicate& pred : form.get_predicates()) {
        if (pred.get_type() == PredicateType::NotContains) {
            // TODO: try to resolve not contains
            std::cerr << "len: Cant solve not contains.\n";
            return l_undef;
        }

        for (const Concat& side : pred.get_params()) {
            bool is_concat = side.size() > 1;

            for (const BasicTerm& var : side) {
                // accept literals
                if (init_aut_ass.is_singleton(var)) {
                    continue;
                }

                // Variables are Sigma* or co-finite
                if(init_aut_ass.at(var)->num_of_states() <= 1 || init_aut_ass.is_co_finite(var, len)) {
                    continue;
                }

                /* move this after preprocessing
                // Variable is not literal
                if(init_aut_ass.at(var)->num_of_states() <= 1 || init_aut_ass.is_co_finite(var, len)) {
                    if (is_concat) {
                        zstring var_name = var.get_name();  // Name of the variable

                        // Check if variable was in any concatenation
                        for (zstring n : concat_vars) {
                            if (n == var_name) {
                                std::cerr << "Not suitable 1.\n";
                                std::cerr << var_name << std::endl;
                                std::cerr << "===========" << std::endl;
                                return false;
                            }
                        }
                        
                        // Note it as a concatenation variable
                        concat_vars.emplace_back(var_name);
                    }
                    continue;
                }
                */

                std::cerr << "len: Not suitable.\n";
                return false;
            }
        }
    }
    std::cerr << "len: Suitable.\n";
    return true;
}

}