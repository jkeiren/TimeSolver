/** \file pes.hh
 * An implementation of Parameterised Equation Systems (PESs)
 * @author Jeroen Keiren
 * @copyright MIT Licence, see the accompanying LICENCE.txt
 */
#ifndef PES_HH
#define PES_HH

#include <map>
#include <string>
#include <vector>
#include "utilities.h"
#include "bidirectional_map.h"
#include "ExprNode.h"
#include "transition.h"

/* From pes.y
 * 		#define (define_list)
 *		CLOCKS :{} (clock_Decl)
 *		CONTROL :{} (atomic_Decl)
 *		INITIALLY :{} (initial_Decl)
 * 		PREDICATE :{} (predicate_Decl)
 * 		START:  (start_Decl)
 * 		EQUATIONS: {} (equation_Defn)
 * 		INVARIANT: (inv_Decl)
 *    TRANSITIONS: (trans_Decl)
 * */

/** Predicate equation system, including timed automata specifics */
class pes {
private:
  /** A Hash table of Clock variables, mapping string names to id values.
   * @see ExprNode.cc. */
  clock_name_to_index_t* m_clocks;

  /** A Hash table of Atomic values used to store discrete state
   * variables, mapping string names to id values.
   * @see ExprNode.cc. */
  atomic_name_to_index_t* m_atomic;

  /** A Hash table of ints storing integer
   * substituations for atomic variables.
   * This maps atomic ids to atomic values, representing
   * the "inital" state for each control (atomic) variable.
   * The map is represented as: (id, val).  0 is the default value.
   * @see ExprNode.cc */
  std::map<std::size_t, atomic_value_t> m_initially;

  /** A Hash table storing the list of declared predicates,
   * matching their label with their expression. */
  std::map<std::string, ExprNode*> m_predicates;

  /** The string label of the starting predicate, which
   * should be label the root ExprNode of the expression tree.
   * @see pes.y and pes.tab.c (parser files). */
  std::string m_start_predicate;

  /** A Hash table storing a list of PES, with their labels
   * and their expressions. */
  std::map<std::string, ExprNode*> m_equations;

  /** This is a vector (list) of all invariants with their
   * ExprNodes.
   * This is constructed by the parser while the ExprNode Trees
   * are being generated.
   * @see pes.y and pes.tab.c (parser files). */
  std::vector<const ExprNode*> m_invariants;

  /** The list of transitions of the state machine
   * from the timed automaton and/or PES description. */
  std::vector<Transition*> m_transitions;

  /** This parameter is the size of the maximum
   * constant (in the clock constraints).  There
   * is one constant for all of the clocks
   * This is modified by the program and the parser. */
  clock_value_t m_max_constant;

  /** This DBM represents the initial DBM. */
  DBM* m_initial_clock_zone;

public:
  pes()
      : m_clocks(new clock_name_to_index_t),
        m_atomic(new atomic_name_to_index_t),
        m_max_constant(0),
        m_initial_clock_zone(nullptr)
  {
  }

  /** Destructor assumes all predicates and invariants have been newed,
   * and that the memory can be freed. */
  ~pes() {
    delete_vector_elements(m_invariants);
    delete_vector_elements(m_transitions);

    // Delete equations
    for (std::map<std::string, ExprNode*>::iterator it = m_equations.begin();
         it != m_equations.end(); it++) {
      delete (it->second);
    }

    // Delete all predicates
    for (std::map<std::string, ExprNode*>::iterator it = m_predicates.begin();
         it != m_predicates.end(); it++) {
      delete (it->second);
    }

    delete m_clocks;
    delete m_atomic;
    delete m_initial_clock_zone;
  }

  /** All clocks declared in this PES */
  const clock_name_to_index_t* clocks() const { return m_clocks; }

  /** Add clock with name @name */
  std::size_t add_clock(const std::string& name) {
    std::size_t idx = m_clocks->size() + 1;
    m_clocks->insert(name, idx);
    return idx;
  }

  /** Find the index of clock with name @name */
  std::size_t lookup_clock(const std::string& name) const {
    try {
      return m_clocks->at(name);
    } catch (std::out_of_range&) {
      throw std::out_of_range("Clock variable " + name + " not defined.");
    }
  }

  /** Print all clocks to @os */
  void print_clocks(std::ostream& os) const {
    const std::map<std::string, std::size_t> m(m_clocks->left());
    for (std::map<std::string, std::size_t>::const_iterator it = m.begin();
         it != m.end(); ++it) {
      os << it->first << ":" << it->second << "  ";
    }
  }

  /** Getter for all atomic variables */
  const atomic_name_to_index_t* atomic() const { return m_atomic; }

  /** Insert an atomic variable with label s and initial value
   * v into the list of atomic variables and give it an id.
   * This method gives the atomic variable the use-specified value i.
   * @param s The label for the atomic value.
   * @param v The value of the atomic variable labeled by name, default 0.
   * @return 1 when done. */
  int add_atomic(const char* s, const atomic_value_t v = 0) {
    std::string name(s);
    std::size_t idx = m_atomic->size();
    m_atomic->insert(name, idx);
    m_initially.insert(std::make_pair(idx, v));
    return 1;
  }

  /** Find the index of the atomic variable @name */
  std::size_t lookup_atomic(const std::string& name) const {
    try {
      return m_atomic->at(name);
    } catch (std::out_of_range&) {
      throw std::out_of_range("Clock variable " + name + " not defined.");
    }
  }

  /** Print all atomic variables to @os */
  void print_atomic(std::ostream& os) const {
    const std::map<std::string, std::size_t> m(m_atomic->left());
    for (std::map<std::string, std::size_t>::const_iterator it = m.begin();
         it != m.end(); ++it) {
      os << it->first << ":" << it->second << "  ";
    }
  }

  /** Get the assignment of initial values */
  const std::map<std::size_t, atomic_value_t>& initially() const
  {
    return m_initially;
  }

  /** Get the declared predicates */
  const std::map<std::string, ExprNode*>& predicates() const {
    return m_predicates;
  }

  /** Adds an empty PREDICATE expression to the list of
   * predicates. This list is later used to conjunct
   * equation expressions to these PREDICATE variables, providing a clean
   * way to terminate a predicate expression terminated due to circularity.
   * @note This method is only used in the parser (pes.y)
   * when forming ExprNode trees.
   * @param name The label of the predicate to add.
   * @param i The integer index of the predicate.
   * @return 1 when done. */
  int add_predicate(const char* s) {
    std::string name(s);
    std::size_t i    = m_predicates.size();
    ExprNode*   pred = new ExprNode(PREDICATE, s, i, m_clocks, m_atomic);
    m_predicates.insert(std::make_pair(name, pred));
    return 1;
  }

  /** Looks up a predicate with label s and returns the expression in
   * the list if it is there. Throws a runtime error otherwise.
   * @param s (*) The label of the predicate to look up.
   * @return The reference to the Expression that the predicate is if in the
   * list and nullptr otherwise.
   * @throws runtime error when predicate variable not found. */
  ExprNode* lookup_predicate(const std::string& name) const {
    std::map<std::string, ExprNode*>::const_iterator it =
        m_predicates.find(name);
    if (it != m_predicates.end()) {
      return it->second;
    } else {
      throw std::runtime_error("open predicate variable found: " + name);
    }
  }

  /** Prints out the list of predicate variables (without their right hand
   * side equations) to @os. */
  void print_predicates(std::ostream& os) const {
    for (std::map<std::string, ExprNode*>::const_iterator it =
             m_predicates.begin();
         it != m_predicates.end(); ++it) {
      os << it->first << "  "
         << "ind: " << (it->second)->getIntVal() << "  ";
    }
  }

  /** Get the predicate for which we need to solve */
  std::string& start_predicate() { return m_start_predicate; }

  /** Sets or changes the parity and the block number of a given
   * predicate ExprNode in the list of predicates.
   * @param name The key to look up the ExprNode in the ExprNode list
   * @param block The desired block number of the equation (predicate
   * expression)
   * @param parity The desired parity: true = gfp, false = lfp.
   * @return true:if successful (found the predicate expression),
   * false:otherwise. */
  void set_parity_block(const std::string& name, const int block,
                        const bool parity)
  {
    std::map<std::string, ExprNode*>::const_iterator it =
        m_predicates.find(name);
    if (it != m_predicates.end()) {
      it->second->set_Parity(parity);
      it->second->set_Block(block);
    } else {
      throw std::runtime_error("Predicate variable " + name + " not declared.");
    }
  }

  /** Get the equations */
  const std::map<std::string, ExprNode*>& equations() const {
    return m_equations;
  }

  /** Adds an an equation, with its variable name and right hand side, to
   * the list of equations. This list links predicate variable expressions
   * with their right hand side equations. This separation of
   * predicates from equations provides a clean
   * way to terminate a predicate expression terminated due to circularity
   * and a clean way to delete expressions.
   * @param block The block number for the equation.
   * @param parity The equation's parity: true = gfp, false = lfp.
   * @param name The equation label.
   * @param e (*) The expression of the RHS of the equation.
   * @return 1 if successful in doing so and 0 otherwise. */
  void add_equation(const int block, const bool parity, const std::string& name,
                    ExprNode* e)
  {
    set_parity_block(name, block, parity);
    m_equations.insert(make_pair(name, e));
  }

  /** Tries to find the RHS expression of an equation with a given predicate
   * variable label,
   * and returns the equation, or throws runtime error if there is no such equation.
   * @param s (*) The label of the equation.
   * @return The Expression (a reference) if found in the list, or nullptr if not
   * found in the list of equations.
   * @throws runtime_error when no equation found. */
  ExprNode* lookup_equation(const std::string& name) const {
    std::map<std::string, ExprNode*>::const_iterator it =
        m_equations.find(name);
    if (it != m_equations.end()) {
      return it->second;
    } else {
      throw std::runtime_error("open predicate variable found: " + name);
    }
  }

  /** Get all invariants */
  const std::vector<const ExprNode*>& invariants() const
  {
    return m_invariants;
  }

  /** Add an invariant */
  void add_invariant(ExprNode* inv) { m_invariants.push_back(inv); }

  /** Get all transitions of the TA */
  const std::vector<Transition*>& transitions() const { return m_transitions; }

  /** Add a transition to the TA */
  void add_transition(Transition* t) { m_transitions.push_back(t); }

  /** Get the largest constant in the system */
  clock_value_t max_constant() const { return m_max_constant; }

  /** Update the largest constant in the system (if needed) */
  void update_max_constant(const clock_value_t v)
  {
    m_max_constant = std::max(m_max_constant, v);
  }

  /** Set the intial clock zone.
   *  @pre initial_clock_zone == nullptr */
  void set_initial_clock_zone(DBM* dbm) {
    assert(m_initial_clock_zone == nullptr);
    m_initial_clock_zone = dbm;
    m_initial_clock_zone->setIsCfFalse();
    m_initial_clock_zone->cf();
  }

  /** Returns the initial clock zone.
   *  If the initial clock zone has not been initialized, it is here initialized
   *  to be the clock zone assigning 0 to all clocks */
  DBM* initial_clock_zone() {
    if (m_initial_clock_zone == nullptr) {
      m_initial_clock_zone = new DBM(clocks());
      for (DBM::size_type i = 0; i < m_initial_clock_zone->clocks_size(); ++i) {
        m_initial_clock_zone->addConstraint(i, 0, zero_le);
      }
      m_initial_clock_zone->cf();
    }

    return m_initial_clock_zone;
  }

  /* Create the initial substituation list,
   * either empty or from the initial list
   * that was generated by the parser. */
  SubstList initial_state() const {
    SubstList sublist(atomic()->size(), atomic());
    for (size_t i = 0; i < atomic()->size(); ++i) {
      std::map<std::size_t, atomic_value_t>::const_iterator it = initially().find(i);
      sublist[i] = (*it).second;
    }
    return sublist;
  }

};

#endif // PES_HH
