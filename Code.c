// Nikhil Tudaha
// 19CS10045

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>

typedef struct NFA_
{
    unsigned int n, m, s, f;
    // n X m table containing subset of states.
    unsigned int **delta;
}
NFA;

typedef struct SetOfStates_
{
    unsigned int *A;
    int n; // Size of the array = ceil(number of states / 32)
}
SetOfStates;

typedef struct DFA_
{
    unsigned int n, m, s;
    unsigned int **delta;
    SetOfStates f;
}
DFA;


// These are also used, but are not much relevant for the assignment, so I have implemented them at the end.
typedef struct Node_ Node;
typedef Node * Stack;
void init(Stack *s);
void push(Stack *s, int data);
int pop(Stack *s);
int is_empty(Stack *s);


NFA *readNFA(const char *filename)
{
    FILE *input = fopen(filename, "r");
    if (input == NULL)
    {
        printf("File doesn\'t exist!\n");
        exit(1);
    }
    
    NFA *N = (NFA *) malloc(sizeof(N));
    // s and f are subsets of Q (which is from 0 to n - 1) represented as required.
    fscanf(input, "%d %d", &N->n, &N->m);

    int x = 0;
    // reading the start states.
    fscanf(input, "%d", &x);
    while (x != -1)
    {
        // change the i'th bit of s to 1.
        N->s |= (1U << x);
        fscanf(input, "%d", &x);
    } 

    // reading the final states.
    fscanf(input, "%d", &x);
    while (x != -1)
    {
        // change the i'th bit of f to 1.
        N->f |= (1U << x);
        fscanf(input, "%d", &x);
    } 

    // reading the transition map.
    N->delta = (unsigned int **) calloc(N->n, sizeof(unsigned int *));
    for (int i = 0; i < N->n; i++)
    {
        (N->delta)[i] = (unsigned int *) calloc(N->m, sizeof(unsigned int));
    }
    fscanf(input, "%d", &x);
    while (x != -1)
    {
        int a = 0, q = 0;
        fscanf(input, "%d %d", &a, &q);
        (N->delta)[x][a] |= (1U << q);
        fscanf(input, "%d", &x);
    }
    fclose(input);
    return N;
}

void printNFA(NFA *N)
{
    printf("    Number of States : %d\n", N->n);
    printf("    Input Alphabet : {");
    for (int i = 0; i < N->m; i++)
    {
        printf("%d%s", i, (i == N->m - 1 ? ("}\n") : (", ")));
    }
    printf("    Start States: {");
    for (int i = 0; i < 32; i++)
    {
        if (N->s & (1U << i))
        {
            printf("%d%s", i, (N->s > (1U << (i + 1))) ? (", ") : (""));
        }
    }
    printf("}\n");
    printf("    Final States: {");
    for (int i = 0; i < 32; i++)
    {
        if (N->f & (1U << i))
        {
            printf("%d%s", i, (N->f > (1U << (i + 1))) ? (", ") : (""));
        }
    }
    printf("}\n");
    printf("    Transition Function:\n");
    for (int i = 0; i < N->n; i++)
    {
        for (int j = 0; j < N->m; j++)
        {
            printf("        Delta(%d, %d) = {", i, j);
            for (int k = 0; k < 32; k++)
            {
                if ((N->delta)[i][j] & (1U << k))
                {
                    printf("%d%s", k, ((N->delta)[i][j] > (1U << (k + 1))) ? (", ") : (""));
                }
            }
            printf("}\n");
        }
    }
    printf("\n");
    return;
}

void cleanNFA(NFA *N)
{
    // clean delta.
    for (int i = 0; i < N->n; i++)
    {
        free(N->delta[i]);
    }
    free(N->delta);
    // clean the storage for the struct.
    free(N);
    return;
}

DFA *subsetcons(NFA *N)
{
    DFA *D = (DFA *) malloc(sizeof(DFA));

    // States in DFA as (2 ^ Q), where Q is the number of states in the NFA
    D->n = 1U << (N->n);
    // Input alphabet and start state (which is a subset of states of the NFA, just like it was in the NFA) remain same. 
    // Also same is the case with the transition table.
    D->m = N->m;
    D->s = N->s;

    D->delta = (unsigned int **) calloc(D->n, sizeof(unsigned int *));
    for (int i = 0; i < D->n; i++)
    {
        (D->delta)[i] = (unsigned int *) calloc(D->m, sizeof(unsigned int));
    }
    for (int i = 0; i < D->n; i++)
    {
        for (int j = 0; j < D->m; j++)
        {
            // Go through all the states of NFA present in this DFA.
            for (int k = 0; k < N->n; k++)
            {
                if (i & (1U << k))
                {
                    // Put all the states in D->delta that are reachable from the state k of the NFA with this alphabet.
                    (D->delta)[i][j] |= (N->delta)[k][j]; 
                }
            }
        }
    }

    // Make a set of final states.
    (D->f).n = (D->n + 31) / 32; // Number of members in array = ceil(number of DFA states) / 32
    (D->f).A = (unsigned int *) calloc((D->f).n, sizeof(unsigned int));
    for (int i = 0; i < D->n; i++)
    {
        if (i & (N->f))
        {
            // The state of the DFA i, if it has any intersection with the set of \
            final states in the NFA, then it is included in the final states of the DFA.
            ((D->f).A)[i / 32] |= (1U << (i % 32));
        }
    }

    return D;
}

void printDFA(DFA *D)
{
    printf("    Number of States : %d\n", D->n);
    printf("    Input Alphabet : {");
    for (int i = 0; i < D->m; i++)
    {
        printf("%d%s", i, (i == (D->m - 1) ? ("}\n") : (", ")));
    }
    printf("    Start State: %d\n", D->s);
    unsigned int f = 0;
    for (int i = 0; i < D->n; i++)
    {
        if (((D->f).A)[i / 32] & (1U << (i % 32)))
        {
            f++;
        }
    }
    if (f > 64)
    {
        printf("    Count of Final States : %d\n", f);
    }
    else
    {
        printf("    Final States: {");
        int flag = 0;
        for (int i = 0; i < D->n; i++)
        {
            if (((D->f).A)[i / 32] & (1U << (i % 32)))
            {
                printf("%s%d", ((flag == 0) ? "" : ", "), i);
                flag = 1;
            }
        }
        printf("}\n");
    }
    printf("    Transition Function: ");
    if (D->n > 64)
    {
        printf("Skipped\n\n");
        return;
    }
    printf("\n    a\\p |");
    for (int i = 0; i < D->n; i++)
    {
        printf(" %3d", i);
    }
    printf("\n");
    printf("    ");
    for (int i = 0; i < 4 * D->n + 5; i++)
    {
        if (i == 4)
        {
            printf("+");
        }
        else
        {
            printf("-");
        }
    }
    printf("\n");
    for (int i = 0; i < D->m; i++)
    {
        printf("    %3d |", i);
        for (int j = 0; j < D->n; j++)
        {
            printf(" %3d", (D->delta)[j][i]);
        }
        printf("\n");
    }
    printf("\n");
    return;
}

SetOfStates *findreachable(DFA *D)
{
    int count = 0;
    // Get a visited bool (int 0/1) array.
    int *visited = (int *) calloc(D->n, sizeof(int));
    // Using DFS, so we will need a stack.
    Stack dfs;
    init(&dfs);
    // Start the DFS
    push(&dfs, D->s);
    visited[D->s] = 1;
    while (!is_empty(&dfs))
    {
        int state = pop(&dfs);
        // Put all its neighbours, i.e. valid transition from here under some alphabet.
        for (unsigned int i = 0; i < D->m; i++)
        {
            if (!visited[(D->delta)[state][i]])
            {
                push(&dfs, (D->delta)[state][i]);
                visited[(D->delta)[state][i]] = 1;
            }
        }
    }
    for (unsigned int i = 0; i < D->n; i++)
    {
        if (visited[i])
        {
            count++;
        }
    }
    SetOfStates *R = (SetOfStates *) malloc(sizeof(SetOfStates));
    R->n = (D->n + 31) / 32; // size of the array R.A
    R->A = (unsigned int *) calloc(R->n, sizeof(unsigned int));
    unsigned int pos = 0;
    for (unsigned int i = 0; i < D->n; i++)
    {
        if (visited[i])
        {
            (R->A)[i / 32] |= (1U << (i % 32));
        }
    }
    printf("+++ Reachable States: {");
    int flag = 0;
    for (int i = 0; i < D->n; i++)
    {
        if ((R->A)[i / 32] & (1U << (i % 32)))
        {
            printf("%s%d", (flag == 0) ? ("") : (", "), i);
            flag = 1;
        }
    }
    printf("}\n\n");
    free(visited);
    return R;
}

DFA *rmunreachable(DFA *D, SetOfStates *R)
{
    // First we make a reverse mapping from old state name to new state name.
    // R_inv[old] = new, as old will appear on index old in the R array.
    unsigned int *R_arr = (unsigned int *) calloc(32 * R->n, sizeof(unsigned int));
    unsigned int *R_inv = (unsigned int *) calloc(D->n, sizeof(unsigned int));
    unsigned int nR = 0;
    // nR is the number of reachable states, and thus, the number of states in the resultant DFA.
    for (unsigned int i = 0; i < D->n; i++)
    {
        if ((R->A)[i / 32] & (1U << (i % 32)))
        {
            R_inv[i] = nR;
            R_arr[nR++] = i;
        }
        else
        {
            R_inv[i] = -1;
        }
    }
    DFA *rD = (DFA *) malloc(sizeof(DFA));
    rD->n = nR;
    rD->m = D->m;
    rD->s = R_inv[D->s];
    rD->delta = (unsigned int **) calloc(nR, sizeof(unsigned int *));
    for (int i = 0; i < nR; i++)
    {
        (rD->delta)[i] = (unsigned int *) calloc(rD->m, sizeof(unsigned int));
    }
    // Now we renumber the states in delta.
    for (int i = 0; i < nR; i++)
    {
        for (int j = 0; j < D->m; j++)
        {
            // State R[i] of original DFA, alphabet j and state i of new DFA.
            // if it is a reachable state, define delta for it.
            (rD->delta)[i][j] = R_inv[(D->delta)[R_arr[i]][j]];
        }
    }
    // Now we set the final state.
    (rD->f).n = (rD->n + 31) / 32;
    (rD->f).A = (unsigned int *) calloc((rD->f).n, sizeof(unsigned int));
    for (int i = 0; i < nR; i++)
    {
        // check if this state is a final state, using the D->f of original DFA.
        if (((D->f).A)[R_arr[i] / 32] & (1U << (R_arr[i] % 32)))
        {
            ((rD->f).A)[i / 32] |= (1U << (i % 32));
        }
    }
    free(R_arr);
    free(R_inv);
    return rD;
}

unsigned int **findequiv(DFA *D)
{
    unsigned int **M = (unsigned int **) calloc(D->n, sizeof(unsigned int *));
    for (int i = 0; i < D->n; i++)
    {
        M[i] = (unsigned int *) calloc(D->n, sizeof(unsigned int));
    }
    // Now we implement the algorithm.
    for (int i = 0; i < D->n; i++)
    {
        for (int j = i; j < D->n; j++)
        {
            if (i == j)
            {
                continue;
            }
            // If one of them is final and the other isn't, these cannot be equivalent.
            if ((((D->f).A[i / 32] & (1U << (i % 32))) > 0) ^ (((D->f).A[j / 32] & (1U << (j % 32))) > 0))
            {
                M[i][j] = M[j][i] = 1;
            }
        }
    }
    int count = 0;
    do
    {
        count = 0;
        // for all pairs, check if some alphabet makes them go to unequivalent states.
        for (int i = 0; i < D->n; i++)
        {
            for (int j = i; j < D->n; j++)
            {
                if (M[i][j] == 1)
                {
                    continue;
                }
                for (int k = 0; k < D->m; k++)
                {
                    // If delta(i, k) and delta(j, k) cannot be equaivalent, i and j cannot be equivalent.
                    if (M[(D->delta)[i][k]][(D->delta)[j][k]] == 1)
                    {
                        M[i][j] = M[j][i] = 1;
                        
                        count++;
                    }
                }
            }
        }
    }
    while (count != 0);
    return M;
}

DFA *collapse(DFA *D, unsigned int **M)
{
    unsigned int *visited = (unsigned int *) calloc(D->n, sizeof(unsigned int));
    // To store if the given state is added in the group.
    unsigned int *group = (unsigned int *) calloc(D->n, sizeof(unsigned int));
    // group[x] will give the group of x.
    unsigned int current_group = 0;
    // To store the group number of a given state.
    printf("+++ Equivalent States :\n");
    for (int i = 0; i < D->n; i++)
    {
        if (visited[i])
        {
            continue;
        }
        visited[i] = 1;
        printf("    Group %3d : {%d", current_group, i);
        group[i] = current_group;
        for (int j = i + 1; j < D->n; j++)
        {
            if (!M[i][j])
            {
                group[j] = current_group;
                visited[j] = 1;
                printf(", %d", j);
            }
        }
        current_group++;
        printf("}\n");
    }
    printf("\n");
    unsigned int *group_inv = (unsigned int *) calloc(current_group, sizeof(unsigned int));
    // group_inv[x] will give a member of the old DFA which is present in the x group
    free(visited);
    visited = (unsigned int *) calloc(D->n, sizeof(unsigned int));
    current_group = 0;
    for (int i = 0; i < D->n; i++)
    {
        if (visited[i])
        {
            continue;
        }
        visited[i] = 1;
        group_inv[current_group] = i;
        for (int j = i + 1; j < D->n; j++)
        {
            if (!M[i][j])
            {
                visited[j] = 1;
            }
        }
        current_group++;
    }
    DFA *D_collapsed = (DFA *) malloc(sizeof(DFA));
    D_collapsed->n = current_group;
    D_collapsed->m = D->m;
    D_collapsed->s = group[D->s];
    // The final state.
    (D_collapsed->f).n = (current_group + 31) / 32;
    (D_collapsed->f).A = (unsigned int *) calloc(((D_collapsed)->f).n, sizeof(unsigned int));
    for (int i = 0; i < D->n; i++)
    {
        if ((D->f).A[i / 32] & (1U << (i % 32)))
        {
            (D_collapsed->f).A[group[i] / 32] |= (1U << (group[i] % 32));
        }
    }
    // The transition function.
    D_collapsed->delta = (unsigned int **) calloc(D->n, sizeof(unsigned int *));
    for (int i = 0; i < D_collapsed->n; i++)
    {
        (D_collapsed->delta)[i] = (unsigned int *) calloc(D_collapsed->m, sizeof(unsigned int));
    }
    for (int i = 0; i < D_collapsed->n; i++)
    {
        for (int j = 0; j < D_collapsed->m; j++)
        {
            (D_collapsed->delta)[i][j] = group[(D->delta)[group_inv[i]][j]];
        }
    }
    free(visited);
    free(group);
    free(group_inv);
    return D_collapsed;
}

void cleanDFA(DFA *D)
{
    // clean delta.
    for (int i = 0; i < D->n; i++)
    {
        free(D->delta[i]);
    }
    free(D->delta);
    // clean the dynamic array in f.
    free((D->f).A);
    free(D);
    return;
}

void clean(NFA *N, DFA *D, SetOfStates *R, DFA *Dr, unsigned int **M, DFA *Dc)
{
    // Clean NFA.
    cleanNFA(N);
    // Clean DFA.
    cleanDFA(D);
    // clean the SetOfStates object.
    free(R->A);
    free(R);
    for (int i = 0; i < Dr->n; i++)
    {
        free(M[i]);
    }
    free(M);
    cleanDFA(Dr);
    cleanDFA(Dc);
    return;
}

int main()
{
    printf("Enter the filename of the input file: ");
    char filename[20];
    scanf("%s", filename);
    clock_t begin = clock();
    NFA *N = readNFA(filename);
    printf("+++ Input NFA\n");
    printNFA(N);
    DFA *D = subsetcons(N);
    printf("+++ Converted DFA\n");
    printDFA(D);
    SetOfStates *R = findreachable(D);
    DFA *D_reachable = rmunreachable(D, R);
    printf("+++ Reduced DFA after removing Unreachable States\n");
    printDFA(D_reachable);
    unsigned int **M = findequiv(D_reachable);
    DFA *D_collapsed = collapse(D_reachable, M);
    printf("+++ Reduced DFA after collapsing Equivalent States\n");
    printDFA(D_collapsed);
    clean(N, D, R, D_reachable, M, D_collapsed);
    clock_t end = clock();
    double time = (double) (end - begin) / CLOCKS_PER_SEC;
    printf("Executed in %lf seconds\n", time);
    return 0;
}

struct Node_
{
    int data;
    Node *next;
};

void init(Stack *s)
{
    *s = NULL;
    return;
}

void push(Stack *s, int data)
{
    Node *top = (Node *) malloc(sizeof(Node));
    top->data = data;
    top->next = *s;
    *s = top;
    return;
}

int pop(Stack *s)
{
    if (is_empty(s))
    {
        exit(1);
    }
    int top = (*s)->data;
    Node *new_top = (*s)->next;
    free(*s);
    *s = new_top;
    return top;
}

int is_empty(Stack *s)
{
    return (*s == NULL);
}
