#ifndef _NOODLER_LENGTH_DECISION_PROCEDURE_H_
#define _NOODLER_LENGTH_DECISION_PROCEDURE_H_

#include <memory>
#include <deque>
#include <algorithm>

#include "smt/params/theory_str_noodler_params.h"

#include "formula.h"
#include "inclusion_graph.h"
#include "aut_assignment.h"
#include "formula_preprocess.h"
#include "decision_procedure.h"

namespace smt::noodler {

    class VarConstraint
    {
    private:
        zstring _name;
        std::vector<Concat> _constr_eqs;	// All sides of equations on the opposite side of this variable

        std::vector<zstring> _lits; // Literals occuring explicitly and in contained variables

        // std::map<zstring, zstring>& conv;
        bool check_side(const Concat& side);
        void emplace(const Concat& c, std::map<zstring, zstring>& lit_conversion);

        void get_alignments(const std::vector<zstring>& side_lits);
    public:
        lbool is_parsed;
        VarConstraint() : _name(), is_parsed (l_false) {};
        VarConstraint(zstring name) : _name(std::move(name)), is_parsed (l_false) {};
        bool add(const Predicate& pred, std::map<zstring, zstring>& lit_conversion);
        std::string to_string() const;

        // !!! Must be called after parse !!!
        const std::vector<zstring>& get_lits() const;


        // TODO: already generate here
        /**
         * @brief parse var constraint
         * 
         * @param pool all var constraints
         * @param conv conversions for literals
         * @return bool success
         */
        bool parse(std::map<zstring,VarConstraint>& pool, std::map<zstring,zstring>& conv);

        
    };


    /**
     * @brief Length-based decision procedure.
     * 
     */
    class LengthDecisionProcedure : public AbstractDecisionProcedure {
    private:
        std::unordered_set<BasicTerm> init_length_sensitive_vars;
        Formula formula;
        AutAssignment init_aut_ass;
        const theory_str_noodler_params& m_params;

        std::map<zstring, zstring> lit_conversion {};	// Naming literals differently from their value

        // the length formula from preprocessing, get_lengths should create conjunct with it
        LenNode preprocessing_len_formula = LenNode(LenFormulaType::TRUE,{});
        LenNode computed_len_formula = LenNode(LenFormulaType::TRUE,{});
        std::vector<LenNode> implicit_len_formula = {};

    public:
        static zstring generate_lit_alias(const zstring& value, std::map<zstring, zstring>& lit_conversion);
        
        /**
         * Initialize a new decision procedure that can solve language (dis)equality constraints.
         * 
         * @param equalities encodes the language equations
         * @param init_aut_ass gives regular constraints (maps each variable from @p form to some NFA)
         * @param init_length_sensitive_vars the variables that occur in length constraints in the rest of formula
         * @param par Parameters for Noodler string theory.
         */
        LengthDecisionProcedure(const Formula &form, AutAssignment init_aut_ass,
                           const std::unordered_set<BasicTerm>& init_length_sensitive_vars,
                           const theory_str_noodler_params& par
         ) : init_length_sensitive_vars{ init_length_sensitive_vars },
             formula { form },
             init_aut_ass{ init_aut_ass },
             m_params(par) { 
            
            /**
             * TODO
             */
        }

        lbool compute_next_solution() override;
        LenNode get_initial_lengths() override {
            return LenNode(LenFormulaType::TRUE);
        }
        std::pair<LenNode, LenNodePrecision> get_lengths() override;
        void init_computation() override;

        lbool preprocess(PreprocessType opt = PreprocessType::PLAIN, const BasicTermEqiv &len_eq_vars = {}) override;

        static bool is_suitable(const Formula &form, const AutAssignment& init_aut_ass);

        void add_to_pool(std::map<zstring, VarConstraint>& pool, const Predicate& pred);

    };
}

#endif
