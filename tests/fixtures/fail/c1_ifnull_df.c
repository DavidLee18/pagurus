/* FAIL: a maybe-null join is not known-null; the second free is a DF
   on the path that did not assign NULL. */
void *malloc(unsigned long n);
void free(void *p);

int main(int argc, char **argv) {
    int *p = malloc(4);
    if (argc > 1)
        p = NULL;
    free(p);
    free(p);
    return 0;
}
