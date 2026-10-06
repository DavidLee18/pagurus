/* FAIL: while always evaluates the condition, even on the exit path.
   consume(p) frees p and returns 0, so the following free(p) is a
   use-after-move / double-free. Loop[cond; body] would skip that. */
void *malloc(unsigned long n);
void free(void *p);
int consume(int *p) { free(p); return 0; }
int main(void) {
    int *p = malloc(4);
    while (consume(p)) {
        p = malloc(4);
    }
    free(p);
    return 0;
}
