/* PASS: assigning null does not store a live pointer, so the name is not that alias. */
void free(void *);

void f(int *a, int *b) {
    free(b);
}

int main(void) {
    int *q = 0;
    f(q = 0, q);
    return 0;
}
