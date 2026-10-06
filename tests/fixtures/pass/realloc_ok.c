/* PASS: realloc consumes p and yields a fresh owner; free of the result is OK. */
void *malloc(unsigned long);
void *calloc(unsigned long, unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
int main(void){int*p=malloc(4);p=realloc(p,8);free(p);return 0;}
