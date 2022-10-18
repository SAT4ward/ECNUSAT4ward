#include "internal.hpp"
using namespace CaDiCaL;

class SimpleDPLLSATSolver {
private:
public:
  enum State { satisfied, unsatisfied, incompleted, completed };
  class Formula {
  public:
    vector<int> literals; // 1 -> true, -1 -> false
    vector<int> literal_frequency;
    vector<int> literal_polarity;

    vector<vector<int>> clauses;
    Formula() {}

    Formula(const Formula &f) {
      literals = f.literals;
      clauses = f.clauses;
      literal_frequency = f.literal_frequency;
      literal_polarity = f.literal_polarity;
    }

    Formula(int literal_count, const vector<Clause *> &clauses) {
      this->literals.resize(literal_count, 0);
      this->clauses.resize(clauses.size());
      this->literal_frequency.clear();
      this->literal_frequency.resize(literal_count, 0);
      this->literal_polarity.clear();
      this->literal_polarity.resize(literal_count, 0);
      for (unsigned int i = 0; i < clauses.size(); i++)
        for (int j = 0; j < clauses[i]->size; j++) {
          this->clauses[i].push_back(clauses[i]->literals[j]);
          int literal_idx = abs(clauses[i]->literals[j]) - 1;
          this->literal_frequency[literal_idx]++;
          if (clauses[i]->literals[j] > 0)
            this->literal_polarity[literal_idx]++;
          else
            this->literal_polarity[literal_idx]--;
        }
    }
  };

  int literal_count;
  int result;
  SimpleDPLLSATSolver(int literal_count, const vector<Clause *> &clauses) {
    this->literal_count = literal_count;
    Formula formula(literal_count, clauses);
    if (DPLL(formula) == State::incompleted) {
      show_result(formula, State::unsatisfied);
    }
  }

  int apply_transform(Formula &f, int literal_to_apply) {
    int value_to_apply = f.literals[literal_to_apply];
    assert(value_to_apply == 1 || value_to_apply == -1);
    for (int i = 0; i < f.clauses.size(); i++) {
      for (int j = 0; j < f.clauses[i].size(); j++) {
        if (f.clauses[i][j] == (literal_to_apply + 1) * value_to_apply) {
          f.clauses.erase(f.clauses.begin() + i);
          i--;
          if (f.clauses.size() == 0)
            return State::satisfied;
          break;
        } else if (f.clauses[i][j] ==
                   (literal_to_apply + 1) * value_to_apply * -1) {
          f.clauses[i].erase(f.clauses[i].begin() + j);
          j--;
          if (f.clauses[i].size() == 0)
            return State::unsatisfied;
          break;
        }
      }
    }
    return State::incompleted;
  }

  int unit_propagate(Formula &f) {
    bool unit_clause_found = false;
    if (f.clauses.size() == 0)
      return State::satisfied;
    do {
      unit_clause_found = false;
      for (int i = 0; i < f.clauses.size(); i++) {
        if (f.clauses[i].size() == 1) {
          unit_clause_found = true;
          int literal_idx = abs(f.clauses[i][0]) - 1;
          f.literals[literal_idx] = f.clauses[i][0] > 0 ? 1 : -1;
          f.literal_frequency[literal_idx] = -1;
          int result = apply_transform(f, literal_idx);
          if (result == State::satisfied || result == State::unsatisfied)
            return result;
          break;
        } else if (f.clauses[i].size() == 0)
          return State::unsatisfied;
      }
    } while (unit_clause_found);
    return State::incompleted;
  }

  int DPLL(Formula f) {
    int result = unit_propagate(f);
    if (result == State::satisfied) {
      show_result(f, result);
      return State::completed;
    } else if (result == State::unsatisfied)
      return State::incompleted;
    int i = distance(
        f.literal_frequency.begin(),
        max_element(f.literal_frequency.begin(), f.literal_frequency.end()));
    for (int j = 0; j < 2; j++) {
      Formula new_f = f;
      if (new_f.literal_polarity[i] > 0)
        new_f.literals[i] = (j == 0 ? 1 : -1);
      else
        new_f.literals[i] = (j == 0 ? -1 : 1);
      new_f.literal_frequency[i] = -1;
      int transform_result = apply_transform(new_f, i);
      if (transform_result == State::satisfied) {
        show_result(new_f, transform_result);
        return State::completed;
      } else if (transform_result == State::unsatisfied)
        continue;
      int dpll_result = DPLL(new_f);
      if (dpll_result == State::completed)
        return dpll_result;
    }
    return State::incompleted;
  }

  void show_result(Formula &f, int result) {
    cout << endl;
    if (result == State::satisfied) {
      cout << "SATISFIABLE" << endl;
      for (int i = 0; i < f.literals.size(); i++) {
        if (i != 0) {
          cout << " ";
        }
        if (f.literals[i] != 0)
          cout << f.literals[i] * (i + 1);
        else
          cout << (i + 1);
      }
      cout << " 0";
    } else
      cout << "UNSAT";
    cout << endl;
  }
};

int Internal::dpll_loop_with_inprocessing() {
  //   cout << "clauses:" << endl;
  //   for (unsigned int i = 0; i < clauses.size(); i++) {
  //     for (int j = 0; j < clauses[i]->size; j++)
  //       cout << clauses[i]->literals[j] << " ";
  //     cout << endl;
  //   }
  //   cout << endl << endl;
  int res = SimpleDPLLSATSolver(max_var, clauses).result;
  return res;
}
