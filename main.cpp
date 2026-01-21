#include <bits/stdc++.h>
#include <cstdint>
using namespace std;
#pragma GCC target ("avx2")
#pragma GCC optimization ("O3")
#pragma GCC optimization ("unroll-loops")
#define int int64_t
typedef vector<int> vi;
typedef vector<vi> vvi;
typedef pair<int, int> pii;
typedef vector<pii> vpii;
typedef set<int> s;
#define sz(a) int((a).size())
#define pb push_back
#define all(c) (c).begin(), (c).end()
#define present(c, x) ((c).find(x) != (c).end())
vector<vi> adj;
vector<bool> visited;
#define endl '\n'
vi parent;
vi color;
vi sized;
//#include <ext/pb_ds/assoc_container.hpp>
//#include <ext/pb_ds/tree_policy.hpp>
//using namespace __gnu_pbds;
//template<class T> using ordered_set = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update>;
//only use the above commands with g++23

// ---------- Bit Manipulation ----------
inline int set_bit(int x, int i) { return x | (1LL << i); }
inline int unset_bit(int x, int i) { return x & ~(1LL << i); }
inline int toggle_bit(int x, int i) { return x ^ (1LL << i); }
inline bool check_bit(int x, int i) { return (x >> i) & 1; }
inline int count_set_bits(int x) { return __builtin_popcountll(x); }
inline int count_trailing_zeros(int x) { return x == 0 ? 64 : __builtin_ctzll(x); }
inline int count_leading_zeros(int x) { return x == 0 ? 64 : __builtin_clzll(x); }
inline int get_lsb(int x) { return x & -x; }
inline int get_msb_pos(int x) { return x == 0 ? -1 : 63 - __builtin_clzll(x); }
inline bool is_power_of_two(int x) { return x > 0 && !(x & (x - 1)); }

// Returns (x + y) using bitwise operators
inline int bitwise_add(int x, int y) {
    while (y != 0) {
        int carry = x & y;
        x = x ^ y;
        y = carry << 1;
    }
    return x;
}

// Derived from: A + B = (A ^ B) + 2 * (A & B)
// Given A ^ B (xor_val) and A & B (and_val), returns A + B
inline int sum_from_xor_and(int xor_val, int and_val) {
    return xor_val + 2 * and_val;
}

// Derived from: A | B = (A ^ B) + (A & B)
inline int or_from_xor_and(int xor_val, int and_val) {
    return xor_val + and_val;
}

// ---------- Number Theory ----------
const int mod = 1000000007;

int gcd(int a, int b) { return b == 0 ? a : gcd(b, a % b); }
int lcm(int a, int b) { return (a / gcd(a, b)) * b; }

int modpow(int a, int e, int m = mod) {
    int res = 1, base = a % m;
    while (e > 0) {
        if (e & 1) res = (res * base) % m;
        base = (base * base) % m;
        e >>= 1;
    }
    return res;
}

int inv(int x) { return modpow(x, mod - 2); }

// Sieve of Eratosthenes
vector<int> primes;
vector<bool> is_prime_check;
void sieve(int n) {
    is_prime_check.assign(n + 1, true);
    is_prime_check[0] = is_prime_check[1] = false;
    for (int i = 2; i * i <= n; i++) {
        if (is_prime_check[i]) {
            for (int j = i * i; j <= n; j += i)
                is_prime_check[j] = false;
        }
    }
    for (int i = 2; i <= n; i++) if (is_prime_check[i]) primes.pb(i);
}

// Prime Factorization - O(sqrt(n))
vector<int> get_prime_factors(int n) {
    vector<int> factors;
    while (n % 2 == 0) { factors.pb(2); n /= 2; }
    for (int i = 3; i * i <= n; i += 2) {
        while (n % i == 0) { factors.pb(i); n /= i; }
    }
    if (n > 2) factors.pb(n);
    return factors;
}

// Get all Divisors - O(sqrt(n))
vector<int> get_divisors(int n) {
    vector<int> divs;
    for (int i = 1; i * i <= n; i++) {
        if (n % i == 0) {
            divs.pb(i);
            if (i * i != n) divs.pb(n / i);
        }
    }
    return divs;
}

// Euler's Totient Function - O(sqrt(n))
int phi(int n) {
    int result = n;
    for (int i = 2; i * i <= n; i++) {
        if (n % i == 0) {
            while (n % i == 0) n /= i;
            result -= result / i;
        }
    }
    if (n > 1) result -= result / n;
    return result;
}

bool is_prime_naive(int n) {
    if (n <= 1) return false;
    for (int i = 2; i * i <= n; i++) if (n % i == 0) return false;
    return true;
}

// ---------- Combinatorics Precomputation ----------
static vector<int> fact, ifact;

void factorials(int n) {
    fact.resize(n + 1);
    ifact.resize(n + 1);
    fact[0] = 1;
    for (int i = 1; i <= n; ++i) fact[i] = (fact[i - 1] * i) % mod;
    ifact[n] = inv(fact[n]);
    for (int i = n; i > 0; --i) ifact[i - 1] = (ifact[i] * i) % mod;
}

int nCr(int n, int r) {
    if (r < 0 || r > n) return 0;
    if (sz(fact) <= n) factorials(n);
    return (fact[n] * ifact[r] % mod) * ifact[n - r] % mod;
}

int nPr(int n, int r) {
    if (r < 0 || r > n) return 0;
    if (sz(fact) <= n) factorials(n);
    return (fact[n] * ifact[n - r]) % mod;
}

// ---------- Segment Tree ----------
// Usage: 1. Define 'T' (data type), 'merge' (func: T+T->T), and 'id' (neutral element, e.g., 0 for sum, -INF for max).
//        2. Initialize: SegTree<T> st(initial_data_vector, merge_function, identity_element);
template <typename T>
class SegTree {
public:
    using F = std::function<T(const T&, const T&)>;
    SegTree(const std::vector<T>& data, F merge, T identity) : n(data.size()), f(merge), id(identity) {
        tree.assign(2 * n, id);
        copy(all(data), tree.begin() + n);
        for (int i = n - 1; i > 0; --i) tree[i] = f(tree[i << 1], tree[i << 1 | 1]);
    }
    void update(int pos, const T& val) {
        for (tree[pos += n] = val; pos > 1; pos >>= 1) tree[pos >> 1] = f(tree[pos], tree[pos ^ 1]);
    }
    T query(int l, int r) const {
        T resL = id, resR = id;
        for (l += n, r += n; l < r; l >>= 1, r >>= 1) {
            if (l & 1) resL = f(resL, tree[l++]);
            if (r & 1) resR = f(tree[--r], resR);
        }
        return f(resL, resR);
    }
private:
    int n; vector<T> tree; F f; T id;
};

void fast_io() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
}

int32_t main() {
    fast_io();
    int test = 1;
    // cin >> test;
    while (test--) {
        "lets do competitive programming in dev spring camp !!!";
    }
    return 0;
}