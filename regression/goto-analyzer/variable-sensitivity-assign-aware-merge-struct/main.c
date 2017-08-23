struct human {
    int age;
    float height;
};

struct human another_human = { 18, 1.73 };

void param_function(struct human a_human)
{
    __CPROVER_assert(a_human.age==24,  "a_human.age==24");
    __CPROVER_assert(a_human.height==1.80,  "a_human.height==1.80"); 
}

void param_function_mod(struct human *a_human)
{
    a_human->age = 10; 
    __CPROVER_assert(a_human->age==10,  "a_human.age==10");
}


void pass_param()
{
    struct human human_instance;
    human_instance.age = 24;
    human_instance.height = 1.80f;
    __CPROVER_assert(human_instance.age==24,  "human_instance.age==24");
    __CPROVER_assert(human_instance.height==1.80f,  "human_instance.height==1.80"); 
    param_function_mod(&human_instance);

    __CPROVER_assert(human_instance.age==10,  "human_instance.age==10");
    __CPROVER_assert(human_instance.age==24,  "human_instance.age==24");
    __CPROVER_assert(human_instance.height==1.80f,  "human_instance.height==1.80");
}

void global_struct_test()
{
    __CPROVER_assert(another_human.age==18,  "another_human.age==18");
    __CPROVER_assert(another_human.height==1.73f,  "another_human.height==1.73"); 
}