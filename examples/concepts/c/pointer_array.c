#include <stdint.h>

void simple() {
    int a[10];
    int b[] = {1, 2, 3};
    int c[10][5];
    //@ assume (\forall int i = 0 .. 10; {:a[i]:} == i);
    //@ assert a[5] == 5;
    a[4] = 1;
    //@ assert a[4] == 1;

    //@ assert (\forall int i = 0 .. 3; {:b[i]:} == i + 1);

    //@ assert \pointer_length(c) == 10 * 5;
    //@ assert (uintptr_t)&c == (uintptr_t)c;
    //@ assert (uintptr_t)c == (uintptr_t)&c[0][0];
    //@ assert (uintptr_t)c == (uintptr_t)&c[0];
    //@ assert (uintptr_t)c + 5 * sizeof(int) == (uintptr_t)&c[1];
    //@ assert (uintptr_t)c + 6 * sizeof(int) == (uintptr_t)&c[1][1];

    //@ exhale (\forall* int i = 0 .. 10; Perm({:a[i]:}, write));
    //@ exhale (\forall* int i = 0 .. 3; Perm({:b[i]:}, write));

    // This one does not work yet. We should figure out if we can allow the assumptions created by the initialisation to propagate here. This probably requires some additional mechanism for this in SimplifyNestedQuantifiers
    // exhale (\forall* int i = 0 .. 10, int j = 0 .. 5; Perm({:c[i][j]:}, write));

    // We can of course rewrite it manually
    //@ exhale (\forall* int i = 0 .. 10 * 5; Perm({:*(c + i):}, write));

    //@ [/expect assertFailed:false]
    //@ assert false;
    //@ [/end]
}

//@ requires (\forall* int i = 0 .. n, int j = 0 .. m; Perm({:a[j][i]:}, write));
void fromType(int n, int m, int a[m][n]) {
    //@ assert \pointer_block_length(a) == n * m;
    //@ [/expect assertFailed:false]
    //@ assert false;
    //@ [/end]
}

//@ requires (\forall* int i = 0 .. n; Perm({:a[0][i]:}, write));
void partialFromType(int n, int a[][n]) {
    //@ assert \pointer_block_length(a) >= n;
    //@ [/expect assertFailed:false]
    //@ assert false;
    //@ [/end]
}

//@ requires \pointer_length(a) == n * m;
//@ requires (\forall* int i = 0 .. n, int j = 0 .. m; Perm({:a[j][i]:}, write));
void fromTypeAndContract(int n, int m, int a[][n]) {
    //@ [/expect assertFailed:false]
    //@ assert false;
    //@ [/end]
}

/*@ ghost
ensures \result;
pure _Bool dummy(int x);*/

/*@ ghost
ensures \result;
pure _Bool dummy2(int x, int y);*/

// Provable using smt.arith.solver == 6
/*@ ghost
requires 0 <= i && i < n;
requires 0 <= idx && idx < m * n;
requires idx % n == i;
ensures (idx - i) % n == 0;
ensures 0 <= (idx - i) / n;
ensures (idx - i) / n < m;
ensures \result;
pure _Bool lemma(int n, int m, int i, int idx);*/


// Provable using smt.arith.solver == 6
/*@ ghost
requires 0 <= j && j < m;
requires 0 <= idx - j * n && idx - j * n < n;
ensures 0 <= idx;
ensures idx < m * n;
ensures \result;
pure _Bool lemma2(int n, int m, int j, int idx);*/

// This one is difficult because of the unnatural iteration order
//@ requires n > 0 && m > 0;
//@ context_everywhere (\forall* int i = 0 .. n, int j = 0 .. m; Perm({:a[j][i]:}, write));
//@ ensures (\forall int i = 0 .. n, int j = 0 .. m; {:a[j][i]:} == j * n + i);
void parameterInLoop(int n, int m, int a[m][n]) {
    //@ loop_invariant 0 <= i && i <= n;
    //@ loop_invariant (\forall int k = 0 .. i, int j = 0 .. m; {:a[j][k]:} == j * n + k);
    for (int i = 0; i < n; i++) {
        //@ loop_invariant 0 <= i && i <= n;
        //@ loop_invariant 0 <= j && j <= m;
        //@ loop_invariant (\forall int k = 0 .. i, int l = 0 .. m; {:a[l][k]:} == l * n + k);
        //@ loop_invariant (\forall int l = 0 .. j; {:dummy(l):}; l * n + i < \pointer_block_length(a));
        //@ loop_invariant (\forall int l = 0 .. j; dummy(l); {:a[l][i]:} == l * n + i);
        for (int j = 0; j < m; j++) {
            // Assumption provable within smt.arith.solver == 6
            //@ assume j * n + i < n * m;
            a[j][i] = j * n + i;
        }
        //@ assert (\forall int idx = 0 .. (m * n); idx % n < i; {:*(a + idx):} == (idx / n) * n + (idx % n));
        //@ assert (\forall int idx = 0 .. (m * n); idx % n == i; lemma(n, m, i, idx) ==> {:*(a + idx):} == (idx / n) * n + (idx % n));
    }
}

//@ requires n > 0 && m > 0;
//@ ensures \pointer(\result, m * n, write);
//@ ensures (\forall int i = 0 .. n, int j = 0 .. m; {:\result[j * n + i]:} == j * n + i);
int *localInLoop(int n, int m) {
    int a[m][n];

    //@ loop_invariant (\forall* int k = 0 .. n, int j = 0 .. m; Perm({:a[j][k]:}, write));
    //@ loop_invariant a == \old(a);
    //@ loop_invariant 0 <= i && i <= n;
    //@ loop_invariant (\forall int k = 0 .. i, int j = 0 .. m; {:a[j][k]:} == j * n + k);
    for (int i = 0; i < n; i++) {
        //@ loop_invariant (\forall* int k = 0 .. n, int l = 0 .. m; Perm({:a[l][k]:}, write));
        //@ loop_invariant 0 <= i && i <= n;
        //@ loop_invariant 0 <= j && j <= m;
        //@ loop_invariant (\forall int k = 0 .. i, int l = 0 .. m; {:a[l][k]:} == l * n + k);
        //@ loop_invariant (\forall int l = 0 .. j; {:dummy(l):}; l * n + i < \pointer_block_length(a));
        //@ loop_invariant (\forall int l = 0 .. j; dummy(l); {:a[l][i]:} == l * n + i);
        for (int j = 0; j < m; j++) {
            // Assumption provable within smt.arith.solver == 6
            //@ assume j * n + i < n * m;
            a[j][i] = j * n + i;
        }
        //@ assert (\forall int idx = 0 .. (m * n); idx % n < i; {:*(a + idx):} == (idx / n) * n + (idx % n));
        //@ assert (\forall int idx = 0 .. (m * n); idx % n == i; lemma(n, m, i, idx) ==> {:*(a + idx):} == (idx / n) * n + (idx % n));
    }

    // Not a good example since we're returning stack memory. Once we add leak checks this will fail
    return a;
}

//@ requires n > 0 && m > 0;
//@ context (\forall* int i = 0 .. n, int j = 0 .. m; Perm({:a[j][i]:}, write));
//@ ensures (\forall int i = 0 .. n, int j = 0 .. m; {:a[j][i]:} == j * n + i);
void parameterInParBlock(int n, int m, int a[m][n]) {
    //@ context (\forall* int i = 0 .. n; lemma2(n, m, j, j * n + i); Perm({:a[j][i]:}, write));
    //@ ensures (\forall* int i = 0 .. n; lemma2(n, m, j, j * n + i); {:a[j][i]:} == j * n + i);
    for (int j = 0; j < m; j++) {
        //@ context lemma2(n, m, j, j * n + i) ==> Perm({:a[j][i]:}, write);
        //@ ensures lemma2(n, m, j, j * n + i) ==> {:a[j][i]:} == j * n + i;
        for (int i = 0; i < n; i++) {
            a[j][i] = j * n + i;
        }
    }
}
