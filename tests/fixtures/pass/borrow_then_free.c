/* Passing a pointer to a callee is a borrow in v1, not a move. */
void *malloc(unsigned long n);
void free(void *p);
void inspect(void *p);

int main(void) {
    void *p = malloc(8);
    inspect(p);
    free(p);
    return 0;
}
