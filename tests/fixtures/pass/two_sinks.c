void *malloc(unsigned long);
void *calloc(unsigned long, unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
void s1(void*p){free(p);}
int main(void){int*p=malloc(4);int*q=malloc(4);s1(p);s1(q);return 0;}
