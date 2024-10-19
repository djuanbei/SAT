//
// Created by yun dai on 2024/10/19.
//

#include "Solver.h"

using namespace std;
using namespace sat;

namespace {
BValue simplifyClause(std::vector<Lit> &lits) {

  std::sort(lits.begin(), lits.end());
  auto it = std::unique(lits.begin(), lits.end());
  lits.resize(it - lits.begin());

  if (lits.size() < 2) {
    return B_UN_KNOWN;
  }

  it = lits.begin();
  auto jt = lits.begin() + 1;
  while (jt != lits.end()) {

    if (*it != *jt) {
      if (it->getVar() == jt->getVar()) {
        lits.clear();
        return B_TRUE;
      }
      it++;
      *it = *jt;
    }
    jt++;
  }
  it++;
  lits.resize(it - lits.begin());

  if (lits.empty()) {
    return B_FASE;
  }

  return B_UN_KNOWN;
}
} // namespace

bool Clause::valid() const {

  if (value_.size() < 2) {
    return false;
  }
  for (auto lit : value_) {
    if (lit.isValid()) {
      return false;
    }
  }
  auto tmp = value_;
  std::sort(tmp.begin(), tmp.end());

  for (size_t i = 1; i < tmp.size(); i++) {
    if (tmp[i - 1] == tmp[i]) {
      return false;
    }
    if (isVarPairLit(tmp[i - 1], tmp[i])) {
      return false;
    }
  }

  return true;
}

bool Solver::add(Lit lit) {
  assert(isInitGood());
  assert(lit.isValid());

  return addClauseImpl({lit});
}

bool Solver::add(Lit f, Lit s) {
  assert(isInitGood());
  assert(f.isValid());
  assert(s.isValid());

  if (f == s) {
    return addClauseImpl({f});
  }
  return addClauseImpl({f, s});
}

bool Solver::add(Lit f, Lit s, Lit t) {
  assert(f.isValid());
  assert(s.isValid());
  assert(t.isValid());

  assert(isInitGood());

  return addClauseImpl({f, s, t});
}
bool Solver::add(std::vector<Lit> lits) {
  assert(isInitGood());
#ifndef NDEBUG
  for (auto lit : lits) {
    assert(lit.isValid());
  }
#endif

  return addClauseImpl(lits);
}

SolverStatus Solver::solve() {
  if (getStatus() != UN_SOLVE) {
    return getStatus();
  }
  auto conf = propagation();

  if (conf != nullptr) {
    return UN_SAT;
  }
  SolverStatus s;

  int number_conf = 1000;
  while (true) {

    if ((s = solveLimit(number_conf)) != UN_SOLVE) {
      solver_status_ = s;
      return s;
    }
    number_conf += 100;
  }
}

SolverStatus Solver::solveLimit(int number_conf) {
  int conf_n = 0;
  Clause *conf = nullptr;

  while (conf_n < number_conf) {
    conf = propagation();
    if (conf) {
      /// analysis
      auto lean = analysis(conf);
      if (lean.second < 0) {
        return UN_SAT;
      }
      backToLevel(lean.second);
      auto lean_clause = addClause(lean.first, LEARN);
      ///
      addUnCheckLit(lean.first[0], lean_clause);

    } else {
      /// choose decide lit
      auto lit = chooseOneLit();
      if (!lit.isValid()) {
        return SAT;
      }
      decide();
      addUnCheckLit(lit, nullptr);
    }
  }

  return UN_SOLVE;
}

Clause *Solver::propagation() {
  while (tail_head_ < tail_.size()) {
    auto lit = tail_[tail_head_];
    auto neg_lit = ~lit;
    Lit new_watch;
    auto &ws = watch_list_[lit];

    for (auto &w : ws) {
      if (w.isRemove()) {
        continue;
      }
      if (getValue(w.getOther())) {
        // have sat
        continue;
      }
      auto watch_clause = w.getClause();

      if (watch_clause->getValue()[0] == neg_lit) {
        watch_clause->getValue()[1] = neg_lit;
      }
      // [2,...) lit find new water lit
      size_t i = 2;
      for (; i < watch_clause->getValue().size(); i++) {
        if (!isFalse(watch_clause->getValue()[i])) {
          break;
        }
      }
      if (i < watch_clause->getValue().size()) {
        new_watch = watch_clause->getValue()[i];
        /// remove watch clause watch_clause in lit watch list
        /// add watch_clause in  ~new_watch watch list
        watch_clause->getValue()[1] = new_watch;
        watch_clause->getValue()[i] = neg_lit;

        // todo
        removeWatch(ws, watch_clause);

        watch_list_[~new_watch].emplace_back(watch_clause,
                                             watch_clause->getValue()[0]);

        continue;
      }
      // other watch value
      auto o_v = watch_clause->getValue()[0].getVar();

      if (B_UN_KNOWN == getBValue(o_v)) {
        addUnCheckLit(o_v, watch_clause);
      } else {
        // find conflict clause
        return watch_clause;
      }
    }
    tail_head_++;
  }

  return nullptr;
}

std::pair<std::vector<Lit>, int> Solver::analysis(const Clause *conf) {
  assert(conf);
  assert(conf->valid());
  std::vector<char> seen(max_var_id_ + 1, 0);
  int high_level = -1;

  for (auto lit : conf->getValue()) {
    seen[lit.getVar()] = 1;
    if (getLevel(lit.getVar()) > high_level) {

      high_level = getLevel(lit.getVar());
    }
  }

  if (0 == high_level) {
    return {{}, -1};
  }
  Lit high_level_lit;
  for (size_t i = tail_.size(); i >= tail_limit_[high_level]; i--) {
    auto lit = tail_[i];

    if (!seen[lit.getVar()]) {
      continue;
    }

    high_level_lit = lit;

    seen[lit.getVar()] = 0;
    auto rean_cl = reason_[lit.getIndex()];
    if (rean_cl) {
      for (size_t i = 1; i < rean_cl->getValue().size(); i++) {
        auto tmp_lit = rean_cl->getValue()[i];
        assert(!seen[tmp_lit.getVar()]);
        seen[tmp_lit.getVar()] = 1;
      }
    }
  }

  std::vector<Lit> lean_clause;
  lean_clause.push_back(~high_level_lit);
  int second_high_leval = 0;

  for (size_t v = 0; v < seen.size(); v++) {
    if (seen[v]) {
      if (getLevel(v) > second_high_leval) {
        second_high_leval = v;
      }

      lean_clause.emplace_back(v, getBValue(v) == B_FASE);
    }
  }

  return {lean_clause, second_high_leval};
}

Lit Solver::chooseOneLit() {
  while (!var_order_.empty()) {
    auto last = var_order_.back();
    var_order_.pop_back();
    if (value_[last] != B_UN_KNOWN) {
      if (rand() % 2 == 1) {
        return Lit(last, true);
      } else {
        return Lit(last, false);
      }
    }
  }

  return {};
}

void Solver::decide() { tail_limit_.push_back(tail_.size()); }

bool Solver::addClauseImpl(std::vector<Lit> lits, ClauseOrigin origin) {

  if (origin != LEARN) {
    int old_max_id = max_var_id_;
    for (auto lit : lits) {
      if (lit.getVar() > max_var_id_) {
        max_var_id_ = lit.getVar();
      }
    }
    for (auto v = old_max_id; v < max_var_id_; v++) {
      var_order_.push_back(v);
    }
    if (max_var_id_ > old_max_id && max_var_id_ + 1 > level_.size()) {
      extandVar(1.3 * (max_var_id_ + 1) + 5);
    }
  }

  if (origin == FORMULA) {
    auto s = simplifyForInput(lits);
    if (s != B_UN_KNOWN) {
      return s;
    }
  }

  if (lits.empty()) {
    solver_status_ = UN_SAT;
    return false;
  }

  if (1 == lits.size()) {
    addUnCheckLit(level_[0], nullptr);
    return true;
  }

  addClause(lits, origin);

  return true;
}

Clause *Solver::addClause(const std::vector<Lit> &lits, ClauseOrigin origin) {
  assert(lits.size() > 1);

  auto cl = new Clause(lits, origin);
  clauses_.push_back(cl);
  Watcher w1(cl, lits[1]);
  Watcher w2(cl, lits[0]);

  watch_list_[~lits[0]].push_back(w1);
  watch_list_[~lits[1]].push_back(w2);
  return cl;
}

// todo
void Solver::backToLevel(int level) {
  assert(tail_limit_.size() >= level);
  if (tail_limit_.size() == level) {
    return;
  }

  if (level == 0) {
    return;
  }

  for (size_t k = level; k < tail_limit_.size(); k++) {
    var_order_.push_back(tail_[tail_limit_[k]].getVar());
  }

  int loc = tail_limit_[level - 1];

  for (size_t i = tail_.size() - 1; i >= loc; i--) {
    auto lit = tail_[i];
    value_[lit.getVar()] = B_UN_KNOWN;
  }

  tail_limit_.resize(level);

  tail_.resize(loc);
  tail_head_ = tail_.size();
}
//// return false iff it find the lits is false
BValue Solver::simplifyForInput(std::vector<Lit> &lits) const {
  assert(isInitGood());

  if (simplifyClause(lits) == B_TRUE) {
    return B_TRUE;
  }

  auto it = lits.begin();
  auto jt = lits.begin();
  while (jt != lits.end()) {
    if (value_[jt->getVar()] == jt->getVarBValue()) {
      lits.clear();
      return B_TRUE;
    } else if (value_[jt->getVar()] != (~(jt->getVarBValue()))) {
      it++;
      *it = *it;
    }
    jt++;
  }
  it++;
  lits.resize(it - lits.begin());
  return lits.empty() ? B_FASE : B_UN_KNOWN;
}

void Solver::extandVar(int new_max_num) {
  assert(new_max_num > max_var_id_);

  value_.resize(new_max_num, B_UN_KNOWN);
  level_.resize(new_max_num, -1);
  reason_.resize(2 * new_max_num, nullptr);
}

void Solver::resetStatus() {
  if (solver_status_ != UN_SAT) {
    if (!tail_limit_.empty()) {
      tail_.erase(tail_.begin() + tail_limit_[0], tail_.end());
    }
    tail_limit_.clear();
    solver_status_ = UN_SOLVE;
  }
}

std::vector<BValue> Solver::getModel() const {
  assert(getStatus() == SAT);
  if (getStatus() == SAT) {
    std::vector<BValue> model(getVarNum(), B_UN_KNOWN);
    for (auto &lit : tail_) {
      model[lit.getVar()] = lit.getVarBValue();
    }
    return model;
  }
  return {};
}
