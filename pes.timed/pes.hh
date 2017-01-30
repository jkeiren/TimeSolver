#ifndef PES_HH
#define PES_HH

#include <map>
#include <string>
#include <vector>
#include "bidirectional_map.hh"
#include "ExprNode.hh"
#include "transition.hh"

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

class pes
{
  protected:
    /** A Hash table of Clock variables, mapping string names to id values.
     * @see ExprNode.cc. */
    bidirectional_map<std::string, int> _clocks;

    /** A Hash table of Atomic values used to store discrete state
     * variables, mapping string names to id values.
     * @see ExprNode.cc. */
    bidirectional_map<std::string, int> _atomic;

    /** A Hash table of ints storing integer
     * substituations for atomic variables.
     * This maps atomic ids to atomic values, representing
     * the "inital" state for each control (atomic) variable.
     * The map is represented as: (id, val).  0 is the default value.
     * @see ExprNode.cc */
    std::map <int, int> _initially;

    /** A Hash table storing the list of declared predicates,
     * matching their label with their expression. */
    std::map <std::string, ExprNode*> _predicates;

    /** The string label of the starting predicate, which
     * should be label the root ExprNode of the expression tree.
     * @see pes.y and pes.tab.c (parser files). */
    std::string _start_predicate;

    /** A Hash table storing a list of PES, with their labels
     * and their expressions. */
    std::map <std::string, ExprNode*> _equations;

    /** This is a vector (list) of all invariants with their
     * ExprNodes.
     * This is constructed by the parser while the ExprNode Trees
     * are being generated.
     * @see pes.y and pes.tab.c (parser files). */
    std::vector<ExprNode*> _invariants;

    /** The list of transitions of the state machine
     * from the timed automaton and/or PES description. */
    std::vector<Transition*> _transitions;

  public:
    pes()
    {}

    /** Destructor assumes all predicates and invariants have been newed,
     * and that the memory can be freed. */
    ~pes()
    {
    }

    /** Explicit function to free data structures that have been malloc'ed in the
     *  parser. This is to avoid double frees */
    void free_all_pointers()
    {
      // Delete all allocated invariants
      for(std::vector<ExprNode *>::iterator it = _invariants.begin();
          it != _invariants.end(); it++) {
        delete *it;
      }

      // Delete Transitions in transition list
      for(std::vector<Transition*>::iterator it = _transitions.begin();
        it != _transitions.end(); ++it)
      {
        delete *it;
      }

      // Delete equations
      for(std::map<std::string, ExprNode*>::iterator it = _equations.begin();
          it != _equations.end(); it++) {
        delete (it->second);
      }

      // Delete all predicates
      for(std::map<std::string, ExprNode *>::iterator it = _predicates.begin();
          it != _predicates.end(); it++) {
        delete (it->second);
      }
    }

    /** All clocks declared in this PES */
    const bidirectional_map<std::string, int>& clocks() const
    {
      return _clocks;
    }

    /** Number of clocks, including the implicit 0 clock x0 */
    int spaceDimension() const
    {
      return _clocks.size() + 1;
    }

    /** Add clock with name @name */
    int add_clock(const std::string& name)
    {
      int idx = _clocks.size() + 1;
      _clocks.insert(name, idx);
      return idx;
    }

    /** Find the index of clock with name @name */
    int lookup_clock(const std::string& name) const
    {
      try
      {
        return _clocks.at(name);
      }
      catch(std::out_of_range& )
      {
        return -1;
      }
    }

    /** Print all clocks to @os */
    void print_clocks(std::ostream& os) const
    {
      const std::map<std::string, int> m(_clocks.left());
      for(std::map<std::string, int>::const_iterator it = m.begin(); it != m.end(); ++it)
      {
        os << it->first << ":" << it->second << "  ";
      }
    }

    const bidirectional_map<std::string, int>& atomic() const
    {
      return _atomic;
    }

    /** Insert an atomic variable with label s and initial value
     * v into the list of atomic variables and give it an id.
     * This method gives the atomic variable the use-specified value i.
     * @param s The label for the atomic value.
     * @param v The value of the atomic variable labeled by name, default 0.
     * @return 1 when done. */
    int add_atomic(const char* s, const int v = 0)
    {
      std::string name(s);
      int idx = _atomic.size();
      _atomic.insert(name, idx);
      _initially.insert(std::make_pair(idx, v));
      return 1;
    }

    int lookup_atomic(const std::string& name) const
    {
      try
      {
        return _atomic.at(name);
      }
      catch (std::out_of_range&)
      {
        return -1;
      }
    }

    /** Print all atomic variables to @os */
    void print_atomic(std::ostream& os) const
    {
      const std::map<std::string, int> m(_atomic.left());
      for(std::map<std::string, int>::const_iterator it = m.begin(); it != m.end(); ++it)
      {
        os << it->first << ":" << it->second << "  ";
      }
    }

    const std::map <int,int>& initially() const
    {
      return _initially;
    }

    const std::map <std::string, ExprNode*>& predicates() const
    {
      return _predicates;
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
    int add_predicate(const char* s)
    {
      std::string name(s);
      int i = _predicates.size();
      ExprNode* pred = new ExprNode(PREDICATE, s, i, _clocks, _atomic);
      _predicates.insert(std::make_pair(name, pred));
      return 1;
    }

    /** Looks up a predicate with label s and returns the expression in
     * the list if it is there and NULL otherwise.
     * @param s (*) The label of the predicate to look up.
     * @return The reference to the Expression that the predicate is if in the
     * list and NULL otherwise. */
    ExprNode* lookup_predicate(const std::string& name) const
    {
      std::map<std::string, ExprNode *>::const_iterator it = _predicates.find(name);
      if (it != _predicates.end())
      {
        return it->second;
      }
      else
      {
        return nullptr;
      }
    }

    /** Prints out the list of predicate variables (without their right hand
     * side equations) to @os. */
    void print_predicates(std::ostream& os) const
    {
      for (std::map <std::string, ExprNode *>::const_iterator it = _predicates.begin();
           it != _predicates.end(); ++it){
        os << it->first << "  ";
        os << "ind: " << (it->second)->getIntVal() << "  ";
      }
    }

    std::string& start_predicate()
    {
      return _start_predicate;
    }

    /** Sets or changes the parity and the block number of a given
     * predicate ExprNode in the list of predicates.
     * @param name The key to look up the ExprNode in the ExprNode list
     * @param block The desired block number of the equation (predicate expression)
     * @param parity The desired parity: true = gfp, false = lfp.
     * @return true:if successful (found the predicate expression),
     * false:otherwise. */
    bool set_parity_block(const std::string& name, const int block, const bool parity)
    {
      std::map<std::string, ExprNode*>::const_iterator it = _predicates.find(name);
      if (it != _predicates.end()){
        it->second->set_Parity(parity);
        it->second->set_Block(block);
        return true;
      }
      else
      {
        return false;
      }
    }

    const std::map<std::string, ExprNode*>& equations() const
    {
      return _equations;
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
    bool add_equation(const int block, const bool parity, const std::string& name, ExprNode *e)
    {
      if(set_parity_block(name, block, parity)){
        _equations.insert(make_pair(name, e));
        return true;
      }
      else
        return false;
    }

    /** Tries to find the RHS expression of an equation with a given predicate
     * variable label,
     * and returns the equation, or NULL if there is no such equation.
     * @param s (*) The label of the equation.
     * @return The Expression (a reference) if found in the list, or NULL if not
     * found in the list of equations. */
    ExprNode* lookup_equation(const std::string& name) const
    {
      std::map<std::string, ExprNode*>::const_iterator it = _equations.find(name);
      if (it != _equations.end())
      {
        return it->second;
      }
      else
      {
        return nullptr;
      }
    }

    const std::vector<ExprNode*>& invariants() const
    {
      return _invariants;
    }

    void add_invariant(ExprNode* inv)
    {
      _invariants.push_back(inv);
    }

    const std::vector<Transition*>& transitions() const
    {
      return _transitions;
    }

    void add_transition(Transition* t)
    {
      _transitions.push_back(t);
    }
};

#endif // PES_HH