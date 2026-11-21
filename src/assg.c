#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "assg.h"

/* =====================================================================
 * Node storage
 * ===================================================================== */

/* Milestone only: nodes live in a fixed-size static pool instead of being
 * malloc'd. Because they are static, they must never be passed to free(). */
#define MAX_NODES 100
static Node node_pool[MAX_NODES];
static int node_count = 0;   /* how many pool slots have been handed out */

/* Creates and initialises a node. Computes f = g + h and stores the parent
 * pointer (used later to reconstruct the final path).
 * Returns NULL if the pool is exhausted. */
Node *create_node(int x, int y, int g, int h, Node *parent) {
    /* Milestone: use pool. For the final submission replace with:
     *   Node *n = malloc(sizeof(Node)); (check for NULL) */
    if (node_count >= MAX_NODES) return NULL;
    Node *n = &node_pool[node_count++];   /* take the next unused slot */
    n->x = x;
    n->y = y;
    n->g = g;
    n->h = h;
    n->f = g + h;
    n->parent = parent;
    return n;
}

/* =====================================================================
 * Min-heap (Open List)
 * The heap is stored as an array where the children of index i are at
 * 2i+1 and 2i+2, and the parent of index i is at (i-1)/2.
 * ===================================================================== */

/* Priority comparison implementing the required tie-break rules.
 * Returns true if a should come out of the heap before b:
 *   1. lower f wins
 *   2. then lower h (closer to the goal)
 *   3. then smaller x
 *   4. then smaller y */
static bool node_less(const Node *a, const Node *b) {
    if (a->f != b->f) return a->f < b->f;
    if (a->h != b->h) return a->h < b->h;
    if (a->x != b->x) return a->x < b->x;
    return a->y < b->y;
}

/* Sets up an empty heap with a small starting capacity (it grows on demand). */
void heap_init(MinHeap *heap) {
    heap->size = 0;
    heap->capacity = 16;
    heap->data = malloc(heap->capacity * sizeof(Node *));
}

/* Bubbles the node at `index` up towards the root while it has higher
 * priority than its parent, restoring the min-heap property after an
 * insertion or a key decrease. */
void heapify_up(MinHeap *heap, int index) {
    while (index > 0) {
        int parent = (index - 1) / 2;
        if (node_less(heap->data[index], heap->data[parent])) {
            /* swap child and parent, then continue from the parent's slot */
            Node *t = heap->data[index];
            heap->data[index] = heap->data[parent];
            heap->data[parent] = t;
            index = parent;
        } else {
            break;   /* already in the right place */
        }
    }
}

/* Sinks the node at `index` down the tree, swapping with its
 * highest-priority child until neither child beats it. Used after the root
 * is replaced during extraction. */
void heapify_down(MinHeap *heap, int index) {
    for (;;) {
        int l = 2 * index + 1, r = 2 * index + 2, best = index;
        /* find which of (current, left child, right child) has top priority */
        if (l < heap->size && node_less(heap->data[l], heap->data[best])) best = l;
        if (r < heap->size && node_less(heap->data[r], heap->data[best])) best = r;
        if (best == index) break;   /* heap property holds here */
        Node *t = heap->data[index];
        heap->data[index] = heap->data[best];
        heap->data[best] = t;
        index = best;
    }
}

/* Adds a node at the end of the array (doubling capacity if full), then
 * bubbles it up into position. */
void heap_insert(MinHeap *heap, Node *node) {
    if (heap->size == heap->capacity) {
        int newcap = heap->capacity * 2;
        Node **tmp = realloc(heap->data, newcap * sizeof(Node *));
        if (!tmp) return;   /* allocation failed: leave heap unchanged */
        heap->data = tmp;
        heap->capacity = newcap;
    }
    heap->data[heap->size] = node;
    heap->size++;
    heapify_up(heap, heap->size - 1);
}

/* Removes and returns the highest-priority node (the root), or NULL if the
 * heap is empty. The last element is moved to the root and sunk down. */
Node *heap_extract_min(MinHeap *heap) {
    if (heap->size == 0) return NULL;
    Node *min = heap->data[0];
    heap->size--;
    if (heap->size > 0) {
        heap->data[0] = heap->data[heap->size];  /* move last element to root */
        heapify_down(heap, 0);
    }
    return min;
}

/* Linear search for the node at (x, y). Returns its index in the heap array,
 * or -1 if it is not present. */
int heap_find(const MinHeap *heap, int x, int y) {
    for (int i = 0; i < heap->size; i++)
        if (heap->data[i]->x == x && heap->data[i]->y == y) return i;
    return -1;
}

/* True when the heap holds no nodes. */
bool heap_is_empty(const MinHeap *heap) {
    return heap->size == 0;
}

/* Updates the g and h costs of the node at `index`, recomputes f, and
 * bubbles it up. Only bubbling up is needed because the key can only get
 * smaller (higher priority). */
void heap_decrease_key(MinHeap *heap, int index, int new_g, int new_h) {
    Node *n = heap->data[index];
    n->g = new_g;
    n->h = new_h;
    n->f = new_g + new_h;
    heapify_up(heap, index);
}

/* Releases the heap's pointer array and resets the struct. */
void heap_free(MinHeap *heap) {
    /* Frees only the pointer array (heap-allocated); pool nodes are not freed.
     * In the final version, also free each remaining node here. */
    free(heap->data);
    heap->data = NULL;
    heap->size = 0;
    heap->capacity = 0;
}

/* =====================================================================
 * Closed List (visited set) - a dynamically resizing array of Node pointers
 * ===================================================================== */

/* Sets up an empty closed list with a small starting capacity. */
void closed_list_init(ClosedList *list) {
    list->size = 0;
    list->capacity = 16;
    list->data = malloc(list->capacity * sizeof(Node *));
}

/* Appends a node, doubling the array's capacity when it is full. */
void closed_list_add(ClosedList *list, Node *node) {
    if (list->size == list->capacity) {
        int newcap = list->capacity * 2;
        Node **tmp = realloc(list->data, newcap * sizeof(Node *));
        if (!tmp) return;   /* allocation failed: node is not added */
        list->data = tmp;
        list->capacity = newcap;
    }
    list->data[list->size++] = node;
}

/* True if a node at (x, y) has already been added to the closed list. */
bool closed_list_contains(const ClosedList *list, int x, int y) {
    for (int i = 0; i < list->size; i++)
        if (list->data[i]->x == x && list->data[i]->y == y) return true;
    return false;
}

/* Releases the closed list's pointer array and resets the struct. */
void closed_list_free(ClosedList *list) {
    free(list->data);
    list->data = NULL;
    list->size = 0;
    list->capacity = 0;
}

/* =====================================================================
 * Milestone driver: reads the insertion phase, then processes commands
 * ===================================================================== */

int main(void) {
    MinHeap open;        /* Open List   - targeted by [O] commands */
    ClosedList closed;   /* Closed List - targeted by [C] commands */
    heap_init(&open);
    closed_list_init(&closed);

    char line[256];
    int x, y, g, h, ng;

    /* ---- Insertion phase: "[O] Insert:" header, then "x, y, g, h" lines,
     * ended by the keyword "done". Markers produce no output. ---- */
    while (fgets(line, sizeof line, stdin)) {
        if (strstr(line, "[O] Insert:")) continue;        /* skip header */
        if (strncmp(line, "done", 4) == 0) break;         /* end of phase */
        if (sscanf(line, " %d , %d , %d , %d", &x, &y, &g, &h) == 4) {
            Node *n = create_node(x, y, g, h, NULL);
            if (n) heap_insert(&open, n);
        }
    }

    /* ---- Command phase: one command per line ---- */
    while (fgets(line, sizeof line, stdin)) {
        /* skip leading whitespace, blank lines and the "Commands:" marker */
        char *p = line;
        while (*p == ' ' || *p == '\t') p++;
        if (*p == '\n' || *p == '\r' || *p == '\0') continue;
        if (strncmp(p, "Commands:", 9) == 0) continue;

        /* the tag decides which list the command targets */
        int is_open;
        if (strncmp(p, "[O]", 3) == 0) is_open = 1;
        else if (strncmp(p, "[C]", 3) == 0) is_open = 0;
        else continue;   /* unrecognised line: ignore */
        p += 3;
        while (*p == ' ') p++;   /* p now points at the command name */

        if (strncmp(p, "IsEmpty", 7) == 0) {
            /* prints True/False for whichever list was targeted */
            bool e = is_open ? heap_is_empty(&open) : (closed.size == 0);
            printf("%s\n", e ? "True" : "False");
        } else if (strncmp(p, "Find", 4) == 0) {
            /* Find (x, y): report whether the node is in the targeted list */
            if (sscanf(p + 4, " ( %d , %d )", &x, &y) == 2) {
                bool found = is_open ? (heap_find(&open, x, y) != -1)
                                     : closed_list_contains(&closed, x, y);
                printf("Node (%d, %d) has %sbeen found\n", x, y, found ? "" : "not ");
            }
        } else if (strncmp(p, "DecreaseKey", 11) == 0) {
            /* DecreaseKey (x, y), new_g = N: open list only. h is kept as is. */
            if (sscanf(p + 11, " ( %d , %d ) , new_g = %d", &x, &y, &ng) == 3) {
                int idx = heap_find(&open, x, y);
                if (idx != -1) {
                    int hh = open.data[idx]->h;   /* existing h is unchanged */
                    heap_decrease_key(&open, idx, ng, hh);
                    printf("Decreased key for Node (%d, %d): f = %d, g = %d, h = %d\n",
                           x, y, ng + hh, ng, hh);
                }
            }
        } else if (strncmp(p, "Extract", 7) == 0) {
            /* Extract: pop the best open node, move it to the closed list,
             * and print its details. */
            Node *n = heap_extract_min(&open);
            if (n) {
                closed_list_add(&closed, n);
                printf("Extracted Node (%d, %d), f = %d, g = %d, h = %d\n",
                       n->x, n->y, n->f, n->g, n->h);
            }
        }
    }

    /* release the arrays (pool nodes are static, so they are not freed) */
    heap_free(&open);
    closed_list_free(&closed);
    return 0;
}