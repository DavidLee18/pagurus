/* Passing a pointer to a callee is a borrow, not a move. */
void *malloc(unsigned long n);
void free(void *p);

void inspect(void *p) {
}

int main(void) {
    void *p = malloc(8);
    inspect(p);
    free(p);
    return 0;
}
