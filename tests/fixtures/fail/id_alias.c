void *malloc(unsigned long);
void *calloc(unsigned long, unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
void*id(void*x){return x;}
int main(void){int*p=malloc(4);int*q=id(p);free(p);free(q);return 0;}
