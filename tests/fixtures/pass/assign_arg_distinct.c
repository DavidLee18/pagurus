/* PASS: the assignment is a fresh pointer; the consume is a different owner. */
void *malloc(unsigned long);
void free(void *);

void f(int *a, int *b) {
    free(b);
}

int main(void) {
    int *p = malloc(4);
    int *q = malloc(4);
    f(q = malloc(4), p);
    free(q);
    return 0;
}
