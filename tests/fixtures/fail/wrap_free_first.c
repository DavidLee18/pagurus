void *malloc(unsigned long);
void *calloc(unsigned long, unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
void ff(void*a,void*b){free(a);}
int main(void){int*p=malloc(4);int*q=malloc(4);ff(p,q);free(q);return 0;}
