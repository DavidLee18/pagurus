/* FAIL: a string literal is not a null pointer; free("hi") is UB. */
void *malloc(unsigned long n);
void free(void *p);

int main(void) {
    char *p = "hi";
    free(p);
    return 0;
}
