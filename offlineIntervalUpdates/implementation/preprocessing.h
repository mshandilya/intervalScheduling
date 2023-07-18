/**
This program uses pre-written templates.
The templates have been created before the beginning of the contest and can be found at
https://github.com/mshandilya/cptemplates
**/

// required macros and template
#include <bits/stdc++.h>
using namespace std;

// type definitions
#define vc vector
typedef vc<int> vi;
typedef vc<pair<int, int>> vii;
typedef vc<list<int>> adjList;

template <typename T>
class seg_tree {
    // the segment tree uses 1 based indexing
    // this segment tree uses a pre-ordering storage format for maximising efficiency

private:
    int size;
    function<T(T, T)> merge;
    vc<T> ST;

public:
    seg_tree() {
        size = 0;
        merge = [](T a, T b){return a;};
    }
    seg_tree(int s, vc<T>& seq, function<T(T, T)> m) {
        size = s;
        ST.resize(s<<1);
        merge = m;
        construct(1, 1, s, seq);
    }
    void construct(int pos, int il, int ir, vc<T>& seq) {
        if(il>size)
            return;
        if(il==ir) {
            ST[pos] = seq[il-1];
            return;
        }
        int mid = (il+ir)>>1, lc = pos + 1, rc = pos + ((mid-il+1)<<1);
        construct(lc, il, mid, seq);
        construct(rc, mid+1, ir, seq);
        ST[pos] = rc<=(size<<1)?merge(ST[lc], ST[rc]):ST[lc];
    }
    void update(int pos, T new_val, int at = 1, int il = 1, int ir = -1) {
        if(ir==-1)
            ir = size;
        if(il>size)
            return;
        if(il==ir) {
            ST[at] = new_val;
            return;
        }
        int mid = (il+ir)>>1, lc = at + 1, rc = at + ((mid-il+1)<<1);
        if(pos<=mid)
            update(pos, new_val, lc, il, mid);
        else
            update(pos, new_val, rc, mid+1, ir);
        ST[at] = rc<=(size<<1)?merge(ST[lc], ST[rc]):ST[lc];
    }
    T fetch(int rl, int rr, int pos = 1, int il = 1, int ir = -1) {
        if(ir==-1)
            ir = size;
        if(il==ir or (il==rl and ir==rr))
            return ST[pos];
        int mid = (il+ir)>>1, lc = pos + 1, rc = pos + ((mid-il+1)<<1);
        if(rr<=mid)
            return fetch(rl, rr, lc, il, mid);
        if(rl>mid)
            return fetch(rl, rr, rc, mid+1, ir);
        return merge(fetch(rl, mid, lc, il, mid), fetch(mid+1, rr, rc, mid+1, ir));
    }
};

class preprocess {

private:
    int n;
    vii s_intervals, e_intervals;
    vi pre_traverse, pre_traversal_index, root_indices, hpa, s_indices;
    adjList forward_edges;
    seg_tree<pair<pair<int, int>, int>> st;

    void dfs(int root, int heavy_par, adjList &backward_edges, vi &heavy_children) {
        hpa[root] = heavy_par;
        pre_traversal_index[root] = n - int(pre_traverse.size());
        pre_traverse.push_back(root);
        if (heavy_children[root] == -1)
            return;
        else
            dfs(heavy_children[root], heavy_par, backward_edges, heavy_children);
        for (int i: backward_edges[root]) {
            if (i != heavy_children[root])
                dfs(i, i, backward_edges, heavy_children);
        }
    }

    // this function shall return the index of the last interval which is part of the solution and ends before the queryTime
    // as well as the size of the set from sol to the given index
    pair<int, int> sol_lowerBound(int solFrom, int queryTime) {
        int from = pre_traversal_index[solFrom], to = pre_traversal_index[hpa[solFrom]], size = 0;
        while (!forward_edges[pre_traverse[to]].empty() and
               e_intervals[forward_edges[pre_traverse[to]].front()].second < queryTime) {
            size += (to - from + 1);
            from = pre_traversal_index[forward_edges[pre_traverse[to]].front()];
            to = pre_traversal_index[hpa[forward_edges[pre_traverse[to]].front()]];
        }
        int beg = from, end = to, mid;
        while (beg <= end) {
            mid = (beg + end) / 2;
            if (e_intervals[pre_traverse[mid]].second >= queryTime)
                end = mid - 1;
            else if (mid == end or e_intervals[pre_traverse[mid + 1]].second >= queryTime)
                return make_pair(pre_traverse[mid], size + mid - from + 1);
            else
                beg = mid + 1;
        }
        size += (to - from + 1);
        return make_pair(-1, size);
    }

    // this function shall return the index of the interval which starts after the queryTime and ends first
    int upperBound(int queryTime) {
        int beg = 0, end = n - 1, mid;
        while (beg <= end) {
            mid = (beg + end) / 2;
            if (s_intervals[mid].first <= queryTime)
                beg = mid + 1;
            else if (mid == beg or s_intervals[mid - 1].first <= queryTime)
                return st.fetch(mid + 1, n).second;
            else
                end = mid - 1;
        }
        return -1;
    }

public:
    preprocess(int &size, vii &intervals) {

        //instantiating instance variables
        n = size;
        s_intervals = intervals;
        e_intervals = intervals;
        s_indices.resize(n);
        pre_traversal_index.resize(n);
        hpa.resize(n);
        forward_edges.resize(n);

        // declaring data structures and variables to be used
        queue<int> current_roots;
        vc<pair<pair<int, int>, int>> si(n);
        vi subtree_sizes(n, 1), heavy_children(n, -1);
        adjList backward_edges(n);

        // sort the intervals by their end-time.
        sort(e_intervals.begin(), e_intervals.end(), [](pair<int, int> a, pair<int, int> b) {
            if (a.second < b.second)
                return true;
            else if (b.second < a.second)
                return false;
            else
                return a.first < b.first;
        });
        for (int i = 0; i < n; i++)
            si[i] = make_pair(e_intervals[i], i);

        // creating the forest(edges) alongside storing the subtree sizes and the heavy children of each node
        for (int i = 0; i < n; i++) {
            while (!current_roots.empty() and e_intervals[current_roots.front()].second < e_intervals[i].first) {
                if (heavy_children[i] == -1 or subtree_sizes[heavy_children[i]] < subtree_sizes[current_roots.front()])
                    heavy_children[i] = current_roots.front();
                forward_edges[current_roots.front()].push_back(i);
                backward_edges[i].push_back(current_roots.front());
                subtree_sizes[i] += subtree_sizes[current_roots.front()];
                current_roots.pop();
            }
            current_roots.push(i);
        }

        // storing the roots for each tree in the forest
        while (!current_roots.empty()) {
            root_indices.push_back(current_roots.front());
            current_roots.pop();
        }

        // creating a pre-traversal array based on HLD alongside storing the pre-traversal indices as well as the
        // highest heavy path ancestor
        for (int root: root_indices)
            dfs(root, root, backward_edges, heavy_children);
        reverse(pre_traverse.begin(), pre_traverse.end());

        // sorting the intervals by their starting times and maintaining a segment tree to do range queries on
        // minimum ending time over the intervals
        sort(s_intervals.begin(), s_intervals.end());
        sort(si.begin(), si.end());
        for(int i = 0; i<n; i++)
            s_indices[si[i].second] = i;
        st = seg_tree<pair<pair<int, int>, int>>(n, si, [](pair<pair<int, int>, int> a, pair<pair<int, int>, int> b) {
            if (a.first.second < b.first.second or (a.first.second == b.first.second and a.first.first > b.first.first))
                return a;
            else
                return b;
        });
    }

    // function to add f new intervals and retrieve the new best answer
    int add(int f, vii& n_intervals) {
        int dynamic_answer_start_time = 1, dynamic_answer_from = 0, final_answer = 0;
        sort(n_intervals.begin(), n_intervals.end(), [](pair<int, int> a, pair<int, int> b) {
            if (a.second < b.second)
                return true;
            else if (b.second < a.second)
                return false;
            else
                return a.first < b.first;
        });
        for(int i = 0; i<f; i++) {
            if(n_intervals[i].first >= dynamic_answer_start_time) {
                if(dynamic_answer_from == -1) {
                    //interval added
                    dynamic_answer_start_time = n_intervals[i].second + 1;
                    final_answer++;
                }
                else {
                    auto slb = sol_lowerBound(dynamic_answer_from, n_intervals[i].first);
                    int prev_ind = slb.first, n_ans = slb.second;
                    if ((prev_ind==-1 and n_intervals[i].second < e_intervals[dynamic_answer_from].second) or
                    (prev_ind>=0 and (forward_edges[prev_ind].empty() or
                    e_intervals[forward_edges[prev_ind].front()].second > n_intervals[i].second))) {
                        //the interval in question is being added to the solution
                        dynamic_answer_from = upperBound(n_intervals[i].second);
                        dynamic_answer_start_time = n_intervals[i].second + 1;
                        final_answer += n_ans + 1;
                    }
                }
            }
        }
        if(dynamic_answer_from != -1)
            final_answer += sol_lowerBound(dynamic_answer_from, INFINITY).second;
        return final_answer;
    }

    // function to delete f original intervals
    int del(int f, vi& n_indices) {
        /*
         * Cases to think about:
         *  The interval to be deleted is not part of the solution.
         *  The interval to be deleted was part of the original / new solution.
         *      Then, the query we need to perform is the upperBound query but with the interval in question removed.
         *      Thankfully, we use a segment tree to perform the range queries and therefore, we can make point updates for the same.
         *      However, at the end of deleting all intervals in question, we must move on to reverse those point updates in the segment tree.
         */
        // in order to delete an entry from the segment tree, we simply point update with the dummy variable {{s_i, INFINITY}, i}
        // every deletion would be O(log n) and re-insertions are also O(log n)
        int dynamic_answer_start_time = 1, dynamic_answer_from = 0, final_answer = 0;
        sort(n_indices.begin(), n_indices.end());
        for(int i = 0; i<f; i++) {
            if(e_intervals[n_indices[i]].first >= dynamic_answer_start_time) {
                auto slb = sol_lowerBound(dynamic_answer_from, e_intervals[n_indices[i]].first);
                int prev_ind = slb.first, n_ans = slb.second;
                if (prev_ind != -1)
                    dynamic_answer_start_time = e_intervals[prev_ind].second + 1;
                st.update(s_indices[n_indices[i]], make_pair(make_pair(e_intervals[n_indices[i]].first, INFINITY), n_indices[i]));
                dynamic_answer_from = upperBound(dynamic_answer_start_time - 1);
                final_answer += n_ans;
            }
        }
        if(dynamic_answer_from != -1 and st.fetch(s_indices[dynamic_answer_from], s_indices[dynamic_answer_from]).first.second != INFINITY)
            final_answer += sol_lowerBound(dynamic_answer_from, INFINITY).second;
        for(int i = 0; i<=f; i++)
            st.update(s_indices[n_indices[i]], make_pair(e_intervals[n_indices[i]], n_indices[i]));
        return final_answer;
    }

    int gen_query(int f1, int f2, vii& n_intervals, vi& n_indices) {
        //to do
        int f = f1+f2, dynamic_answer_from = 0, dynamic_answer_start_time = 1, final_answer = 0;
        vc<pair<pair<int, int>, int>> n_int(f);
        for(int i = 0; i<f1; i++)
            n_int[i] = make_pair(n_intervals[i], -1);
        for(int i = 0; i<f2; i++)
            n_int[f1+i] = make_pair(e_intervals[n_indices[i]], n_indices[i]);
        sort(n_int.begin(), n_int.end(), [](pair<pair<int, int>, int> a, pair<pair<int, int>, int> b){
            if (a.first.second < b.first.second)
                return true;
            else if (b.first.second < a.first.second)
                return false;
            else
                return a.first.first < b.first.first;
        });
        for(int i = 0; i<f; i++) {
            if(n_int[i].second == -1) {
                //said interval needs to be added
                if(n_int[i].first.first >= dynamic_answer_start_time) {
                    if (dynamic_answer_from == -1) {
                        //interval added
                        dynamic_answer_start_time = n_int[i].first.second + 1;
                        final_answer++;
                    } else {
                        auto slb = sol_lowerBound(dynamic_answer_from, n_int[i].first.first);
                        int prev_ind = slb.first, n_ans = slb.second;
                        if ((prev_ind == -1 and n_int[i].first.second < e_intervals[dynamic_answer_from].second) or
                            (prev_ind >= 0 and (forward_edges[prev_ind].empty() or
                                                e_intervals[forward_edges[prev_ind].front()].second >
                                                n_int[i].first.second))) {
                            //the interval in question is being added to the solution
                            dynamic_answer_from = upperBound(n_int[i].first.second);
                            dynamic_answer_start_time = n_int[i].first.second + 1;
                            final_answer += n_ans + 1;
                        }
                    }
                }
            }
            else {
                //said interval needs to be deleted
                if(e_intervals[n_int[i].second].first >= dynamic_answer_start_time) {
                    auto slb = sol_lowerBound(dynamic_answer_from, e_intervals[n_int[i].second].first);
                    int prev_ind = slb.first, n_ans = slb.second;
                    if (prev_ind != -1)
                        dynamic_answer_start_time = e_intervals[prev_ind].second + 1;
                    st.update(s_indices[n_int[i].second], make_pair(make_pair(e_intervals[n_int[i].second].first, INFINITY), n_int[i].second));
                    dynamic_answer_from = upperBound(dynamic_answer_start_time - 1);
                    final_answer += n_ans;
                }
            }
        }
        if(dynamic_answer_from != -1 and st.fetch(s_indices[dynamic_answer_from], s_indices[dynamic_answer_from]).first.second != INFINITY)
            final_answer += sol_lowerBound(dynamic_answer_from, INFINITY).second;
        for(int i = 0; i<=f2; i++)
            st.update(s_indices[n_indices[i]], make_pair(e_intervals[n_indices[i]], n_indices[i]));
        return final_answer;
    }

};

/*
* Cases to think about:
 * When the ending time of the current interval in solution is the same as the ending time of the new interval which is being considered to enter into the solution.
*/