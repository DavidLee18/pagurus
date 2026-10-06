/* FAIL (control): do-while evaluates the body then the condition; consume
   on the condition is visible to a later free. */
void *malloc(unsigned long n);
void free(void *p);
int consume(int *p) { free(p); return 0; }
int main(void) {
    int *p = malloc(4);
    do {
        p = malloc(4);
    } while (consume(p));
    free(p);
    return 0;
}
