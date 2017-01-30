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

    /** Destructor assumes all invariants have been newed, and that the memory
     *  can be freed. */
    ~pes()
    {
      _clocks.clear();

      // Delete all allocated invariants
      for(std::vector<ExprNode *>::iterator it = _invariants.begin();
          it != _invariants.end(); it++) {
        delete *it;
      }
      _invariants.clear();
      _transitions.clear();
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
      catch(std::runtime_error& )
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

    bidirectional_map<std::string, int>& atomic()
    {
      return _atomic;
    }

    std::map <int,int>& initially()
    {
      return _initially;
    }

    std::map <std::string, ExprNode*>& predicates()
    {
      return _predicates;
    }

    const std::map <std::string, ExprNode*>& predicates() const
    {
      return _predicates;
    }

    std::string& start_predicate()
    {
      return _start_predicate;
    }

    std::map<std::string, ExprNode*>& equations()
    {
      return _equations;
    }

    const std::map<std::string, ExprNode*>& equations() const
    {
      return _equations;
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
