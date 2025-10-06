#include <algorithm>
#include <chrono>
#include <cmath>
#include <deque>
#include <fstream>
#include <iostream>
#include <limits>
#include <numeric>
#include <set>
#include <sstream>
#include <tuple>
#include <unordered_map>
#include <vector>

using namespace std;

// =========================
// Constants and Data Structures
// =========================

enum AssignmentState : char { UNASSIGNED = 0, TRUE = 1, FALSE = 2 };

// Flattened clause: metadata + slice into literals_pool
struct Clause {
  int start = 0; // start index in literals_pool
  int size = 0;  // number of literals
  int lbd = 0;
  double activity = 0.0;
  bool is_permanent = true;
  bool is_deleted = false;
  int blocker_lit = 0; // fast-skip when this literal is TRUE
  int inline_lits[2];
  bool use_inline = false;
};

// =========================
// CDCL Solver Class
// =========================

class CDCLSolver {
private:
  int num_vars;

  // Flattened literals storage
  vector<int> literals_pool;
  vector<Clause> clauses;
  int original_clause_count;

  vector<char> assignment;
  vector<int> reason;
  vector<int> level;
  vector<double> vsids_score;
  vector<char> phase_cache;
  vector<int> trail_pos;

  vector<int> trail;
  int prop_idx;

  int decision_level;

  // watches store clause indices
  vector<vector<int>> watches;

  // Conflict analysis seen-marking with time-stamping
  vector<uint8_t> seen_stamp;
  uint8_t seen_current = 1;

  const int seen_reset_threshold = INT_MAX / 2; // reset before overflow

  // Per-literal binary implications: for literal L, edges list stores
  // (implied_literal, clause_idx) Example: for clause (a ∨ b), we add edges:
  // (-a -> b), (-b -> a)
  vector<vector<pair<int, int>>> bin_implies;

  double vsids_decay = 0.95;
  double vsids_bump = 1.0;
  double clause_decay = 0.999;
  double clause_bump = 1.0;

  long long conflicts = 0;
  long long nodes = 0;
  long long max_nodes = 200000000;
  long long next_simplify = 30000;

  deque<int> lbd_q;
  long long lbd_q_sum = 0;
  const int lbd_q_size = 50;
  double lbd_avg = 0.0;

  long long restart_count = 0;
  long long next_restart = 100;

  // ====================
  // Indexed max-heap for VSIDS
  // ====================
  vector<int> heap;     // heap array: heap[pos] = var
  vector<int> heap_pos; // heap_pos[var] = pos in heap, -1 if absent

  void heap_swap(int i, int j) {
    int vi = heap[i], vj = heap[j];
    heap[i] = vj;
    heap[j] = vi;
    heap_pos[vi] = j;
    heap_pos[vj] = i;
  }

  void heap_sift_up(int pos) {
    while (pos > 0) {
      int parent = (pos - 1) >> 1;
      if (vsids_score[heap[pos]] > vsids_score[heap[parent]]) {
        heap_swap(pos, parent);
        pos = parent;
      } else
        break;
    }
  }

  void heap_sift_down(int pos) {
    int n = (int)heap.size();
    while (true) {
      int l = (pos << 1) + 1;
      int r = l + 1;
      int largest = pos;
      if (l < n && vsids_score[heap[l]] > vsids_score[heap[largest]])
        largest = l;
      if (r < n && vsids_score[heap[r]] > vsids_score[heap[largest]])
        largest = r;
      if (largest != pos) {
        heap_swap(pos, largest);
        pos = largest;
      } else
        break;
    }
  }

  void heap_insert_var(int var) {
    if (heap_pos[var] != -1)
      return;
    heap_pos[var] = (int)heap.size();
    heap.push_back(var);
    heap_sift_up(heap_pos[var]);
  }

  void heap_remove_var(int var) {
    int pos = heap_pos[var];
    if (pos == -1)
      return;
    int last = heap.back();
    heap.pop_back();
    heap_pos[var] = -1;
    if (pos < (int)heap.size()) {
      heap[pos] = last;
      heap_pos[last] = pos;
      heap_sift_down(pos);
      heap_sift_up(pos);
    }
  }

  void heap_increase_key(int var) {
    int pos = heap_pos[var];
    if (pos == -1)
      return;
    heap_sift_up(pos);
  }

  inline int heap_top() {
    if (heap.empty())
      return 0;
    return heap[0];
  }

  inline int lit_to_idx(int lit) const {
    int v = abs(lit);
    return (lit > 0) ? (2 * v) : (2 * v + 1);
  }

  inline char get_literal_value(int lit) const {
    int var = abs(lit);
    char var_val = assignment[var];
    if (var_val == UNASSIGNED) {
      return UNASSIGNED;
    }
    return (lit > 0) ? var_val : ((var_val == TRUE) ? FALSE : TRUE);
  }

  // 访问子句中的第 i 个文字
  inline int clause_lit(const Clause &C, int i) const {
    return C.use_inline ? C.inline_lits[i] : literals_pool[C.start + i];
  }

  // 设置子句中的第 i 个文字
  inline void clause_set_lit(Clause &C, int i, int lit) {
    if (C.use_inline) {
      C.inline_lits[i] = lit;
    } else {
      literals_pool[C.start + i] = lit;
    }
  }

  // 交换子句中的两个文字
  inline void clause_swap_lit(Clause &C, int i, int j) {
    if (C.use_inline) {
      std::swap(C.inline_lits[i], C.inline_lits[j]);
    } else {
      std::swap(literals_pool[C.start + i], literals_pool[C.start + j]);
    }
  }

public:
  long long get_conflicts() const { return conflicts; }
  long long get_nodes() const { return nodes; }

  CDCLSolver(vector<vector<int>> &initial_cnf, int vars)
      : num_vars(vars), original_clause_count((int)initial_cnf.size()) {
    prop_idx = 0;
    decision_level = 0;
    assignment.resize(num_vars + 1, UNASSIGNED);
    reason.resize(num_vars + 1, -1);
    level.resize(num_vars + 1, 0);
    vsids_score.resize(num_vars + 1, 0.0);
    phase_cache.resize(num_vars + 1, TRUE);
    trail_pos.resize(num_vars + 1, -1);
    watches.resize(2 * num_vars + 2);
    bin_implies.resize(2 * num_vars + 2);
    heap_pos.resize(num_vars + 1, -1);

    // 预先计算总文字数，避免 literals_pool 多次扩容
    size_t total_lits = 0;
    for (const auto &c : initial_cnf)
      total_lits += c.size();
    literals_pool.reserve(total_lits);

    clauses.reserve(initial_cnf.size());
    for (const auto &c : initial_cnf) {
      Clause meta;
      if (c.size() <= 2) {
        // 短子句直接内联存储
        meta.use_inline = true;
        meta.size = (int)c.size();
        for (int i = 0; i < meta.size; i++) {
          meta.inline_lits[i] = c[i];
          vsids_score[abs(c[i])] += 1.0;
        }
      } else {
        // 长子句仍然放在 literals_pool
        meta.use_inline = false;
        meta.start = (int)literals_pool.size();
        meta.size = (int)c.size();
        for (int lit : c) {
          literals_pool.push_back(lit);
          vsids_score[abs(lit)] += 1.0;
        }
      }
      clauses.push_back(meta);

      int cid = (int)clauses.size() - 1;
      Clause &Cnew = clauses.back();
      if (Cnew.size == 2) {
        int a = clause_lit(Cnew, 0);
        int b = clause_lit(Cnew, 1);
        // Add edges: (-a -> b) and (-b -> a)
        bin_implies[lit_to_idx(-a)].push_back({b, cid});
        bin_implies[lit_to_idx(-b)].push_back({a, cid});
      }
    }

    // 初始化堆
    heap.reserve(num_vars);
    for (int v = 1; v <= num_vars; ++v) {
      heap.push_back(v);
      heap_pos[v] = (int)heap.size() - 1;
    }
    for (int i = ((int)heap.size() >> 1) - 1; i >= 0; --i)
      heap_sift_down(i);

    rebuild_watches();

    size_t initial_clauses = clauses.size();
    size_t reserve_factor = 4;
    literals_pool.reserve(literals_pool.size() * reserve_factor);
    clauses.reserve(initial_clauses * reserve_factor);
    seen_stamp.resize(num_vars + 1, 0);
  }

  void rebuild_watches() {
    for (auto &wl : watches)
      wl.clear();

    vector<int> counts(watches.size(), 0);
    for (int i = 0; i < (int)clauses.size(); ++i) {
      if (clauses[i].is_deleted)
        continue;
      Clause &C = clauses[i];
      if (C.size >= 3) {
        counts[lit_to_idx(clause_lit(C, 0))]++;
        counts[lit_to_idx(clause_lit(C, 1))]++;
      }
    }
    for (size_t idx = 0; idx < watches.size(); ++idx)
      if (counts[idx] > 0)
        watches[idx].reserve(counts[idx]);

    for (int i = 0; i < (int)clauses.size(); ++i) {
      if (clauses[i].is_deleted)
        continue;
      Clause &C = clauses[i];

      // Set blocker to the second watched literal by default (fast skip when
      // TRUE)
      if (C.size >= 2) {
        C.blocker_lit = clause_lit(C, min(1, C.size - 1));
      } else {
        C.blocker_lit = 0;
      }

      if (C.size >= 3) {
        watches[lit_to_idx(clause_lit(C, 0))].push_back(i);
        watches[lit_to_idx(clause_lit(C, 1))].push_back(i);
      }
    }
  }

  void add_unit_assignment(int lit, int clause_index) {
    int v = abs(lit);
    char val = (lit > 0) ? TRUE : FALSE;
    assignment[v] = val;
    level[v] = decision_level;
    reason[v] = clause_index;
    trail_pos[v] = (int)trail.size();
    trail.push_back(lit);
    phase_cache[v] = val;
    heap_remove_var(v);
  }

  int propagate() {
    while (prop_idx < (int)trail.size()) {
      int p = trail[prop_idx++];

      // Fast binary implications: p -> q
      {
        auto &edges = bin_implies[lit_to_idx(p)];
        for (const auto &e : edges) {
          int q = e.first;
          int cid = e.second;
          char vq = get_literal_value(q);
          if (vq == UNASSIGNED) {
            add_unit_assignment(q, cid);
          } else if (vq == FALSE) {
            return cid;
          }
        }
      }

      // Non-binary watched clauses on -p
      int neg_p = -p;
      auto &wlist = watches[lit_to_idx(neg_p)];
      size_t j = 0;

      for (size_t i = 0; i < wlist.size(); ++i) {
        int clause_idx = wlist[i];
        if (clauses[clause_idx].is_deleted)
          continue;

        Clause &C = clauses[clause_idx];
        if (C.size == 2)
          continue; // binaries handled by bin_implies

        // Blocker literal: if TRUE, clause is satisfied → keep and skip
        if (C.blocker_lit != 0 && get_literal_value(C.blocker_lit) == TRUE) {
          wlist[j++] = clause_idx;
          continue;
        }

        if (C.size >= 2) {
          // Ensure neg_p is in one of the two watched positions
          if (clause_lit(C, 0) != neg_p && clause_lit(C, 1) == neg_p) {
            clause_swap_lit(C, 0, 1);
            // maintain blocker as the other watched literal
            C.blocker_lit = clause_lit(C, 1);
          }
          // Stale entry: clause no longer watches neg_p → drop
          if (clause_lit(C, 0) != neg_p && clause_lit(C, 1) != neg_p) {
            continue;
          }

          int other = clause_lit(C, 1);
          // If other watcher is TRUE, keep
          if (get_literal_value(other) == TRUE) {
            // blocker is the satisfying watched literal
            C.blocker_lit = other;
            wlist[j++] = clause_idx;
            continue;
          }

          // Try to find replacement watcher among tail literals
          bool moved = false;
          for (int k = 2; k < C.size; ++k) {
            int lk = clause_lit(C, k);
            char vk = get_literal_value(lk);
            if (vk != FALSE) {
              clause_swap_lit(C, 0, k);
              // New watched pair is (lit0, other). Set blocker to the other.
              C.blocker_lit = other;
              watches[lit_to_idx(clause_lit(C, 0))].push_back(clause_idx);
              moved = true;
              break;
            }
          }
          if (moved) {
            // migrated out of current list
            continue;
          }

          // No replacement: unit or conflict on 'other'
          wlist[j++] = clause_idx;
          char ov = get_literal_value(other);
          if (ov == UNASSIGNED) {
            add_unit_assignment(other, clause_idx);
          } else if (ov == FALSE) {
            // truncate current watchlist
            for (size_t k = i + 1; k < wlist.size(); ++k)
              wlist[j++] = wlist[k];
            wlist.resize(j);
            return clause_idx;
          } else {
            // ov == TRUE already handled, but keep blocker consistent
            C.blocker_lit = other;
          }
        } else if (C.size == 1) {
          wlist[j++] = clause_idx;
          int only = clause_lit(C, 0);
          char val = get_literal_value(only);
          if (val == UNASSIGNED) {
            add_unit_assignment(only, clause_idx);
          } else if (val == FALSE) {
            for (size_t k = i + 1; k < wlist.size(); ++k)
              wlist[j++] = wlist[k];
            wlist.resize(j);
            return clause_idx;
          } else {
            C.blocker_lit = only;
          }
        } else {
          for (size_t k = i + 1; k < wlist.size(); ++k)
            wlist[j++] = wlist[k];
          wlist.resize(j);
          return clause_idx;
        }
      }

      wlist.resize(j);
    }
    return -1;
  }

  void backjump(int level_to_keep) {
    while (!trail.empty()) {
      int lit = trail.back();
      int v = abs(lit);
      if (level[v] <= level_to_keep) {
        break;
      }
      trail.pop_back();
      assignment[v] = UNASSIGNED;
      reason[v] = -1;
      level[v] = 0;
      trail_pos[v] = -1;
      if (heap_pos[v] == -1)
        heap_insert_var(v);
    }
    prop_idx = (int)trail.size();
    decision_level = level_to_keep;
  }

  int calculate_lbd(const vector<int> &clause) {
    static vector<char> level_seen;
    static int level_seen_size = 0;
    int max_needed = decision_level + 1;
    if (level_seen_size < max_needed) {
      level_seen.assign(max_needed, 0);
      level_seen_size = max_needed;
    }

    vector<int> touched_levels;
    touched_levels.reserve(min((size_t)max_needed, clause.size()));

    int distinct = 0;
    for (int lit : clause) {
      int lvl = level[abs(lit)];
      if (!level_seen[lvl]) {
        level_seen[lvl] = 1;
        touched_levels.push_back(lvl);
        distinct++;
      }
    }
    for (int lvl : touched_levels)
      level_seen[lvl] = 0;
    return distinct;
  }

  tuple<vector<int>, int, int> analyze_conflict(int conflict_clause_idx) {
    conflicts++;

    if (++seen_current == 0) {
      std::fill(seen_stamp.begin(), seen_stamp.end(), 0);
      seen_current = 1;
    }

    vector<int> learned;
    int count_curr = 0;
    int idx = (int)trail.size();

    vector<int> stack;
    Clause &conflict = clauses[conflict_clause_idx];
    stack.reserve(conflict.size);
    for (int i = 0; i < conflict.size; ++i)
      stack.push_back(clause_lit(conflict, i));

    while (!stack.empty()) {
      int lit = stack.back();
      stack.pop_back();
      int v = abs(lit);
      if (seen_stamp[v] == seen_current)
        continue;
      seen_stamp[v] = seen_current;

      if (level[v] == decision_level) {
        count_curr++;
        int r = reason[v];
        if (r != -1) {
          Clause &R = clauses[r];
          for (int i = 0; i < R.size; ++i) {
            int rl = clause_lit(R, i);
            if (abs(rl) != v)
              stack.push_back(rl);
          }
          bump_clause_activity(r);
        }
      } else {
        learned.push_back(lit);
      }
    }

    int uip = 0;
    while (idx > 0) {
      int lit = trail[--idx];
      int v = abs(lit);
      if (seen_stamp[v] == seen_current) {
        count_curr--;
        if (count_curr == 0) {
          uip = lit;
          break;
        }
        int r = reason[v];
        if (r != -1) {
          Clause &R = clauses[r];
          for (int i = 0; i < R.size; ++i) {
            int rl = clause_lit(R, i);
            if (abs(rl) != v)
              stack.push_back(rl);
          }
          bump_clause_activity(r);
          while (!stack.empty()) {
            int q = stack.back();
            stack.pop_back();
            int w = abs(q);
            if (seen_stamp[w] != seen_current) {
              seen_stamp[w] = seen_current;
              if (level[w] == decision_level)
                count_curr++;
              else
                learned.push_back(q);
            }
          }
        }
      }
    }

    learned.push_back(-uip);
    bump_vsids(learned);

    int backjump_level = 0;
    if (learned.size() > 1) {
      sort(learned.begin(), learned.end() - 1,
           [&](int a, int b) { return level[abs(a)] > level[abs(b)]; });
      backjump_level = level[abs(learned[0])];
      swap(learned[0], learned.back()); // 将 -UIP 放到 learned[0]
    } else {
      backjump_level = 0;
    }

    int lbd = calculate_lbd(learned);
    return make_tuple(learned, backjump_level, lbd);
  }

  void bump_vsids(vector<int> &literals) {
    // Bump variables in learned clause
    for (int lit : literals) {
      int v = abs(lit);
      vsids_score[v] += vsids_bump;
      if (assignment[v] == UNASSIGNED && heap_pos[v] != -1) {
        // Re-heapify upward
        heap_increase_key(v);
      }
    }
    // Periodically rescale to avoid numeric blow-up
    static const double max_thr = 1e100, scale = 1e-100;
    for (int v = 1; v <= num_vars; ++v) {
      if (vsids_score[v] > max_thr) {
        for (int u = 1; u <= num_vars; ++u)
          vsids_score[u] *= scale;
        vsids_bump *= scale;
        break;
      }
    }
  }
  void decay_vsids() {
    // EVSIDS: increase bump weight (decay scores implicitly)
    // Typical decay ~0.95–0.99. You already use 0.95.
    vsids_bump /= vsids_decay;
  }

  void bump_clause_activity(int clause_idx) {
    if (clause_idx >= original_clause_count) {
      clauses[clause_idx].activity += clause_bump;
      if (clauses[clause_idx].activity > 1e20) {
        for (size_t i = original_clause_count; i < clauses.size(); ++i) {
          clauses[i].activity *= 1e-20;
        }
        clause_bump *= 1e-20;
      }
    }
  }

  void clause_activity_decay() { clause_bump /= clause_decay; }

  pair<int, char> choose_literal() {
    // Ensure heap contains all unassigned variables
    if (heap.empty()) {
      for (int v = 1; v <= num_vars; ++v) {
        if (assignment[v] == UNASSIGNED && heap_pos[v] == -1) {
          heap_insert_var(v);
        }
      }
    }

    // Extract best unassigned variable (EVSIDS)
    while (!heap.empty()) {
      int v = heap_top();
      if (assignment[v] == UNASSIGNED) {
        // Polarity: strong phase saving (last assignment), fallback to TRUE
        char pol = phase_cache[v];
        return {v, pol};
      }
      heap_remove_var(v);
    }
    return {0, UNASSIGNED};
  }

  void simplify_db() {
    vector<int> candidates;
    for (size_t i = original_clause_count; i < clauses.size(); ++i) {
      if (clauses[i].is_deleted)
        continue;
      Clause &C = clauses[i];

      // Never delete binaries; keep LBD <= 2 (core) permanently
      if (C.size <= 2 || C.lbd <= 2)
        continue;

      // Protect reason clauses (they support current trail)
      bool is_reason = false;
      for (int v = 1; v <= num_vars; ++v) {
        if (reason[v] == (int)i) {
          is_reason = true;
          break;
        }
      }
      if (is_reason)
        continue;

      candidates.push_back((int)i);
    }

    // Sort by (LBD desc, activity asc, size desc)
    sort(candidates.begin(), candidates.end(), [&](int a, int b) {
      if (clauses[a].lbd != clauses[b].lbd)
        return clauses[a].lbd > clauses[b].lbd;
      if (clauses[a].activity != clauses[b].activity)
        return clauses[a].activity < clauses[b].activity;
      return clauses[a].size > clauses[b].size;
    });

    // Delete 30–50% of candidates; start with 30% to be conservative
    int to_remove = (int)(candidates.size() * 0.3);
    for (int i = 0; i < to_remove; ++i) {
      clauses[candidates[i]].is_deleted = true;
    }

    next_simplify = conflicts + 5000;
  }

  int add_learned_clause_and_assert(const vector<int> &learned_clause_vec,
                                    int lbd) {
    Clause newC;
    newC.size = (int)learned_clause_vec.size();
    newC.lbd = lbd;
    newC.activity = clause_bump;
    newC.is_permanent = (lbd <= 2);
    newC.is_deleted = false;

    int new_idx = (int)clauses.size();

    if (newC.size <= 2) {
      newC.use_inline = true;
      for (int i = 0; i < newC.size; ++i)
        newC.inline_lits[i] = learned_clause_vec[i];
    } else {
      newC.use_inline = false;
      newC.start = (int)literals_pool.size();
      literals_pool.insert(literals_pool.end(), learned_clause_vec.begin(),
                           learned_clause_vec.end());
    }
    clauses.push_back(newC);

    Clause &C = clauses[new_idx];

    // Set blocker to second literal if available, otherwise 0
    C.blocker_lit =
        (C.size >= 2) ? clause_lit(C, 1) : (C.size == 1 ? clause_lit(C, 0) : 0);

    if (C.size == 2) {
      int a = clause_lit(C, 0);
      int b = clause_lit(C, 1);
      bin_implies[lit_to_idx(-a)].push_back({b, new_idx});
      bin_implies[lit_to_idx(-b)].push_back({a, new_idx});
    } else if (C.size >= 3) {
      int lit0 = clause_lit(C, 0);
      int lit1 = clause_lit(C, 1);
      watches[lit_to_idx(lit0)].push_back(new_idx);
      watches[lit_to_idx(lit1)].push_back(new_idx);
    }

    add_unit_assignment(clause_lit(C, 0), new_idx);
    return new_idx;
  }

  static long long luby_unit(long long i) {
    long long k = 1;
    while ((1LL << k) - 1 < i)
      ++k;
    if (i == (1LL << k) - 1)
      return 1LL << (k - 1);
    return luby_unit(i - ((1LL << (k - 1)) - 1));
  }

  pair<bool, unordered_map<int, bool>> solve() {
    decision_level = 0;

    // Luby restart scheduler state (local to solve)
    static long long luby_idx = 1;
    static long long luby_seq = 1;
    static long long conflicts_since_restart = 0;

    auto on_conflict_accounting = [&]() {
      conflicts_since_restart++;
      // Luby-based restart trigger; 32 is a good base "unit"
      if (conflicts_since_restart >= luby_seq * 32) {
        backjump(0);
        conflicts_since_restart = 0;
        luby_idx++;
        luby_seq = luby_unit(luby_idx);
      }
    };

    // Initial unit clauses
    for (int i = 0; i < (int)clauses.size(); ++i) {
      Clause &C = clauses[i];
      if (C.is_deleted)
        continue;
      if (C.size == 1) {
        int lit = clause_lit(C, 0);
        char v = get_literal_value(lit);
        if (v == FALSE)
          return {false, {}};
        if (v == UNASSIGNED)
          add_unit_assignment(lit, -1);
      }
    }

    // Top-level propagation and learning
    while (true) {
      int confl = propagate();
      if (confl == -1)
        break;

      auto [learned, backjump_level, lbd] = analyze_conflict(confl);
      if (learned.empty())
        return {false, {}}; // true UNSAT

      backjump(backjump_level);
      add_learned_clause_and_assert(learned, lbd);

      // Heuristics update
      decay_vsids();
      clause_activity_decay();

      // LBD queue update
      lbd_q.push_back(lbd);
      lbd_q_sum += lbd;
      if ((int)lbd_q.size() > lbd_q_size) {
        lbd_q_sum -= lbd_q.front();
        lbd_q.pop_front();
      }
      if ((int)lbd_q.size() == lbd_q_size)
        lbd_avg = (double)lbd_q_sum / lbd_q_size;

      on_conflict_accounting();
    }

    // Check if all clauses are satisfied
    auto all_clauses_satisfied = [&]() -> bool {
      for (int idx = 0; idx < (int)clauses.size(); ++idx) {
        Clause &C = clauses[idx];
        if (C.is_deleted)
          continue;
        bool sat = false;
        for (int k = 0; k < C.size; ++k) {
          if (get_literal_value(clause_lit(C, k)) == TRUE) {
            sat = true;
            break;
          }
        }
        if (!sat)
          return false;
      }
      return true;
    };

    // Main search loop
    while (true) {
      nodes++;
      if (nodes > max_nodes)
        return {false, {}};

      auto [var, phase] = choose_literal();

      if (var == 0) {
        // No decision var: if not all satisfied, complete model; else SAT
        if (!all_clauses_satisfied()) {
          int v_pick = 0;
          for (int v = 1; v <= num_vars; ++v) {
            if (assignment[v] == UNASSIGNED) {
              v_pick = v;
              break;
            }
          }
          if (v_pick == 0)
            return {false, {}}; // Shouldn't happen
          decision_level++;
          add_unit_assignment((phase_cache[v_pick] == TRUE) ? v_pick : -v_pick,
                              -1);
          continue;
        }
        unordered_map<int, bool> final_assignment;
        for (int v = 1; v <= num_vars; ++v)
          final_assignment[v] = (assignment[v] == TRUE);
        return {true, final_assignment};
      }

      // New decision
      decision_level++;
      add_unit_assignment((phase == TRUE) ? var : -var, -1);

      int confl;
      while ((confl = propagate()) != -1) {
        auto [learned, backjump_level, lbd] = analyze_conflict(confl);
        if (learned.empty())
          return {false, {}}; // true UNSAT

        backjump(backjump_level);
        add_learned_clause_and_assert(learned, lbd);

        // Heuristics update
        decay_vsids();
        clause_activity_decay();

        // LBD queue update
        lbd_q.push_back(lbd);
        lbd_q_sum += lbd;
        if ((int)lbd_q.size() > lbd_q_size) {
          lbd_q_sum -= lbd_q.front();
          lbd_q.pop_front();
        }
        if ((int)lbd_q.size() == lbd_q_size)
          lbd_avg = (double)lbd_q_sum / lbd_q_size;

        on_conflict_accounting();
      }

      // Dynamic restart via LBD (Glucose-style guard)
      if (!lbd_q.empty()) {
        double curr_avg = (double)lbd_q_sum / (double)lbd_q.size();
        if (lbd_avg > 0.0 && lbd_avg * 0.8 > curr_avg) {
          backjump(0);
          // Reset LBD window to avoid immediate retrigger
          lbd_q.clear();
          lbd_q_sum = 0;
        }
      }

      // Periodic clause database reduction
      if (conflicts > next_simplify) {
        simplify_db();
      }
    }
  }
};

// ===================================
// DIMACS Reader and Verification
// ===================================

pair<vector<vector<int>>, int> read_dimacs_cnf(const string &filename) {
  ifstream file(filename);
  if (!file.is_open()) {
    cerr << "c Error: Could not open file " << filename << endl;
    exit(1);
  }
  vector<vector<int>> clauses;
  int max_var = 0;
  string line;
  while (getline(file, line)) {
    if (line.empty() || line[0] == 'c')
      continue;
    if (line[0] == 'p') {
      stringstream ss(line);
      string p, cnf;
      int num_clauses;
      ss >> p >> cnf >> max_var >> num_clauses;
      continue;
    }
    stringstream ss(line);
    vector<int> current_clause;
    int lit;
    while (ss >> lit && lit != 0) {
      current_clause.push_back(lit);
    }
    if (!current_clause.empty()) {
      sort(current_clause.begin(), current_clause.end());
      bool is_tautology = false;
      for (size_t i = 0; i + 1 < current_clause.size(); ++i) {
        if (current_clause[i] == -current_clause[i + 1]) {
          is_tautology = true;
          break;
        }
      }
      if (!is_tautology) {
        current_clause.erase(
            unique(current_clause.begin(), current_clause.end()),
            current_clause.end());
        clauses.push_back(current_clause);
      }
    }
  }
  return {clauses, max_var};
}

bool verify_solution(const vector<vector<int>> &clauses_cnf,
                     const unordered_map<int, bool> &assignment,
                     int /*num_vars*/) {
  for (const auto &clause : clauses_cnf) {
    bool clause_satisfied = false;
    for (int literal : clause) {
      int var = abs(literal);
      bool var_val = assignment.count(var) ? assignment.at(var) : false;
      bool literal_satisfied = (literal > 0) ? var_val : !var_val;
      if (literal_satisfied) {
        clause_satisfied = true;
        break;
      }
    }
    if (!clause_satisfied) {
      cerr << "c Verification Error: Clause NOT satisfied: ";
      for (int lit : clause)
        cerr << lit << " ";
      cerr << "0" << endl;
      return false;
    }
  }
  return true;
}

// =========================
// Main Program
// =========================

int main(int argc, char *argv[]) {
  ios::sync_with_stdio(false);
  cin.tie(nullptr);

  if (argc != 2) {
    cerr << "Usage: " << argv[0] << " <DIMACS_CNF_file>" << endl;
    return 1;
  }

  auto [cnf, num_vars] = read_dimacs_cnf(argv[1]);
  const vector<vector<int>> original_cnf = cnf;
  if (num_vars == 0 && cnf.empty()) {
    cout << "s SATISFIABLE" << endl;
    cout << "v 0" << endl;
    return 0;
  }
  for (const auto &clause : original_cnf) {
    if (clause.empty()) {
      cout << "s UNSATISFIABLE" << endl;
      return 0;
    }
  }

  auto start_time = chrono::high_resolution_clock::now();
  CDCLSolver solver(cnf, num_vars);
  auto [sat, assignment] = solver.solve();

  auto end_time = chrono::high_resolution_clock::now();
  chrono::duration<double> elapsed = end_time - start_time;

  cout << "c ====================================" << endl;
  cout << "c Solver: C++ CDCL (VSIDS flattened clause version)" << endl;
  cout << "c Time taken (耗时): " << elapsed.count() << " seconds" << endl;
  cout << "c Conflicts (冲突数): " << solver.get_conflicts() << endl;
  cout << "c Decisions (决策数): " << solver.get_nodes() << endl;
  cout << "c ====================================" << endl;

  if (sat) {
    cout << "s SATISFIABLE" << endl;
    cout << "v ";
    for (int v = 1; v <= num_vars; ++v) {
      bool val =
          assignment.count(v) ? assignment.at(v) : false; // 未赋值按 false
      cout << (val ? v : -v) << " ";
    }
    cout << "0" << endl;

    if (verify_solution(original_cnf, assignment, num_vars)) {
      cout << "c Verification: Solution is valid." << endl;
    } else {
      cerr << "c FATAL ERROR: Solver returned SAT but solution verification "
              "FAILED!"
           << endl;
      return 2;
    }
  } else {
    cout << "s UNSATISFIABLE" << endl;
  }

  return 0;
}
