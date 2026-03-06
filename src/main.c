/*

ecc compilation process overview:
    - main.c: the program accepts a list of files, which it then reads in.
        each file goes through the following steps:
    - lex.c: the text is split into lexical preprocessing tokens
    - preprocess.c: preprocessing tokens are built into a tree structure reflecting the syntax
        of a preprocessing file. preprocessing directives are then executed.
    - tokenize.c: preprocessing tokens are converted to tokens
    - parse.c: tokens are built into a tree structure reflecting the syntax of a translation unit.
        symbols are identified in the source program.
    - type.c: symbols found in the source have their type definitions analyzed and added as semantics.
    - analyze.c: the syntactic structure is analyzed for invalid semantics and additional semantic
        information is appended to the tree structure.
    - air.c: the syntactic structure is converted into a linear intermediate representation, known as AIR.
        - opt1.c: the optimization phase that runs after this step occurs.
    - localize.c: AIR routines are localized to a particular architecture. ecc only performs localization
        to x86-64. this step primarily adds data location requirements demanded by the constraints of the target.
    - allocate.c: all temporary values in AIR instructions are converted to registers in the target architecture.
        ecc performs a graph-coloring algorithm to assign registers accordingly.
    - x86asm.c: AIR is converted into corresponding x86-64 assembly instructions and directives.
        - opt4.c: the optimization phase that runs after this step occurs.

brief descriptions of the other files in this project:
    - buffer.c: just represents an expandable byte buffer
    - const.c: contains compile-time constant data
    - constexpr.c: evaluates constant expressions using a semantically analyzed syntax tree (i.e., valid for invocation after static analysis)
    - graph.c: adjacency list-based graph implementation
    - log.c: the ol' logger
    - map.c: closed, linear probing-based hash table implementation, also provides an API for interacting with the struct as if it's a set
    - symbol.c: functions for handling the symbol_t struct
    - syntax.c: functions for handling the syntax_component_t struct
    - traverse.c: traversal data structure for syntax_component_t
    - util.c: uncategorized utility functions
    - vector.c: dynamic array implementation

*/

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>

#include <getopt.h>
#include <unistd.h>
#include <sys/wait.h>

#include "ecc.h"

#define OPTION_DESCRIPTION_LENGTH 12

char* PROGRAM_NAME = NULL;
program_options_t opts;

program_options_t* get_program_options(void)
{
    return &opts;
}

static void delete_array(void** arr, size_t length)
{
    for (size_t i = 0; i < length; ++i)
        free(arr[i]);
    free(arr);
}

int usage(void)
{
    printf("Usage: ecc [options] file...\n");
    printf("Options:\n");
    printf("  %-*sDisplay this help message\n", OPTION_DESCRIPTION_LENGTH, "-h");
    printf("  %-*sSet output filepath\n", OPTION_DESCRIPTION_LENGTH, "-o");
    printf("  %-*sCompile, but do not assemble or link\n", OPTION_DESCRIPTION_LENGTH, "-S");
    printf("  %-*sCompile and assemble, but do not link\n", OPTION_DESCRIPTION_LENGTH, "-c");
    printf("  %-*sLink against default GNU libraries\n", OPTION_DESCRIPTION_LENGTH, "-g");
    printf("  %-*sDisplay internal states (tokens, IRs, etc.)\n", OPTION_DESCRIPTION_LENGTH, "-i");
    printf("  %-*sPreprocess\n", OPTION_DESCRIPTION_LENGTH, "-P");
    printf("  %-*sParse\n", OPTION_DESCRIPTION_LENGTH, "-p");
    printf("  %-*sStatic analysis\n", OPTION_DESCRIPTION_LENGTH, "-a");
    printf("  %-*sAIR\n", OPTION_DESCRIPTION_LENGTH, "-A");
    printf("  %-*sLocalized AIR\n", OPTION_DESCRIPTION_LENGTH, "-L");
    printf("  %-*sRegister-allocated AIR\n", OPTION_DESCRIPTION_LENGTH, "-r");
    printf("  %-*sBleeding edge work, if any (warning: very unstable)\n", OPTION_DESCRIPTION_LENGTH, "-x");
    return EXIT_FAILURE;
}

x86_asm_file_t* compile_object(char* filename)
{
    FILE* file = fopen(filename, "r");
    if (!file)
    {
        errorf("file '%s' not found\n", filename);
        return NULL;
    }
    preprocessing_token_t* tokens = lex(file, true);
    if (!tokens) return NULL;

    if (opts.iflag)
    {
        printf("<<lexer output>>\n");
        for (preprocessing_token_t* token = tokens; token; token = token->next)
        {
            pp_token_print(token, printf);
            printf("\n");
        }
    }

    time_t t = time(NULL);

    preprocessing_settings_t settings;
    settings.translation_time = &t;
    settings.filepath = filename;
    char pp_error[MAX_ERROR_LENGTH];
    settings.error = pp_error;
    settings.error[0] = '\0';
    settings.table = NULL;

    if (!preprocess(&tokens, &settings))
    {
        printf("%s", settings.error);
        return NULL;
    }

    if (opts.ppflag)
    {
        pp_token_delete_all(tokens);
        return NULL;
    }

    strlitconcat(tokens);

    tokenizing_settings_t tk_settings;
    tk_settings.filepath = filename;
    char tok_error[MAX_ERROR_LENGTH];
    tk_settings.error = tok_error;
    tk_settings.error[0] = '\0';

    token_t* ts = tokenize(tokens, &tk_settings);
    if (tk_settings.error[0])
    {
        printf("%s", tk_settings.error);
        return NULL;
    }

    pp_token_delete_all(tokens);

    if (opts.iflag)
    {
        printf("<<tokenizer output>>\n");
        for (token_t* t = ts; t; t = t->next)
        {
            token_print(t, printf);
            printf("\n");
        }
    }

    syntax_component_t* tlu = parse(ts);
    if (!tlu) return NULL;

    if (opts.iflag)
    {
        printf("<<syntax tree>>\n");
        print_syntax(tlu, printf);
    }

    if (opts.pflag)
    {
        free_syntax(tlu, tlu);
        token_delete_all(ts);
        return NULL;
    }

    analysis_error_t* type_errors = type(tlu);
    if (type_errors)
    {
        dump_errors(type_errors);
        if (error_list_size(type_errors, false) > 0)
        {
            fclose(file);
            free_syntax(tlu, tlu);
            token_delete_all(ts);
            return NULL;
        }
    }

    if (opts.iflag)
    {
        printf("<<typed syntax tree>>\n");
        print_syntax(tlu, printf);

        printf("<<symbol table>>\n");
        symbol_table_print(tlu->tlu_st, printf);
    }

    analysis_error_t* errors = analyze(tlu);
    if (errors)
    {
        dump_errors(errors);
        if (error_list_size(errors, false) > 0)
        {
            fclose(file);
            free_syntax(tlu, tlu);
            token_delete_all(ts);
            error_delete_all(errors);
            return NULL;
        }
    }

    error_delete_all(errors);

    if (opts.iflag)
    {
        printf("<<semantically-analyzed syntax tree>>\n");
        print_syntax(tlu, printf);

        printf("<<symbol table>>\n");
        symbol_table_print(tlu->tlu_st, printf);
    }

    if (opts.aflag)
    {
        fclose(file);
        free_syntax(tlu, tlu);
        token_delete_all(ts);
        return NULL;
    }

    air_t* air = airinize(tlu);

    if (opts.iflag)
    {
        printf("<<AIR>>\n");
        air_print(air, printf);
    }

    opt1(air, opt1_profile_basic());

    if (opts.iflag)
    {
        printf("<<AIR (optimized)>>\n");
        air_print(air, printf);
    }

    if (opts.aaflag)
    {
        fclose(file);
        air_delete(air);
        free_syntax(tlu, tlu);
        token_delete_all(ts);
        return NULL;
    }

    localize(air, LOC_X86_64);

    if (opts.iflag)
    {
        printf("<<AIR (x86-localized)>>\n");
        air_print(air, printf);
    }

    if (opts.llflag)
    {
        fclose(file);
        air_delete(air);
        free_syntax(tlu, tlu);
        token_delete_all(ts);
        return NULL;
    }

    allocate(air);

    if (opts.iflag)
    {
        printf("<<AIR (register-allocated)>>\n");
        air_print(air, printf);
    }

    if (opts.rflag)
    {
        fclose(file);
        air_delete(air);
        free_syntax(tlu, tlu);
        token_delete_all(ts);
        return NULL;
    }

    x86_asm_file_t* asmfile = x86_generate(air, tlu->tlu_st);

    opt4(asmfile, opt4_profile_basic());

    if (opts.iflag)
    {
        printf("<<x86 assembly code>>\n");
        x86_asm_file_write(asmfile, stdout);
    }

    fclose(file);
    air_delete(air);
    free_syntax(tlu, tlu);
    token_delete_all(ts);

    return asmfile;
}

char* compile(char* filename, char* target)
{
    x86_asm_file_t* asmfile = compile_object(filename);
    if (!asmfile)
        return NULL;
    
    char* asm_filepath = target ? strdup(target) : temp_filepath_gen(".s");

    FILE* out = fopen(asm_filepath, "w");
    x86_asm_file_write(asmfile, out);
    fclose(out);
    x86_asm_file_delete(asmfile);

    if (opts.iflag)
        printf("assembly written to %s\n", asm_filepath);

    return asm_filepath;
}

char* invoke_assembler(char* filename, char* target)
{
    char* obj_filepath = target ? strdup(target) : temp_filepath_gen(".o");

    pid_t as_pid = fork();

    if (as_pid == -1)
    {
        free(obj_filepath);
        errorf("failed to spawn assembler process\n");
        return NULL;
    }

    if (as_pid == 0)
    {
        char* argv[] = { "/usr/bin/x86_64-linux-gnu-as", filename, "-o", obj_filepath, NULL };
        int status = execv(argv[0], argv);
        if (status == -1)
        {
            free(obj_filepath);
            errorf("failed to execute assembler\n");
            exit(EXIT_FAILURE);
        }
    }

    int as_status = EXIT_FAILURE;
    waitpid(as_pid, &as_status, 0);
    as_status = WEXITSTATUS(as_status);

    if (as_status)
    {
        free(obj_filepath);
        errorf("assembler has failed to produce an object file, cannot proceed with compilation\n");
        return NULL;
    }

    if (opts.iflag)
        printf("object written to %s\n", obj_filepath);

    return obj_filepath;
}

char* assemble(char* filename, char* target)
{
    char* asm_filepath = compile(filename, NULL);
    if (!asm_filepath)
        return NULL;
    char* obj_filepath = invoke_assembler(asm_filepath, target);
    remove(asm_filepath);
    free(asm_filepath);
    return obj_filepath;
}

char** find_libraries(void)
{
    char** libraries = calloc(NO_LIBRARIES, sizeof(char*));
    char* buffer = malloc(LINUX_MAX_PATH_LENGTH);
    for (size_t i = 0; i < NO_LIBRARY_SEARCH_DIRECTORIES; ++i)
    {
        const char* directory = LIBRARY_SEARCH_DIRECTORIES[i];
        for (size_t j = 0; j < NO_LIBRARIES; ++j)
        {
            if (libraries[j])
                continue;
            if (directory[0] == '~')
                snprintf(buffer, LINUX_MAX_PATH_LENGTH, "%s%s/%s", get_home_directory(), directory + 1, LIBRARIES[j]);
            else
                snprintf(buffer, LINUX_MAX_PATH_LENGTH, "%s/%s", directory, LIBRARIES[j]);
            if (!file_exists(buffer))
                continue;
            libraries[j] = strdup(buffer);
        }
    }
    free(buffer);
    return libraries;
}

char* linker(char** object_files, size_t object_count, char* target)
{
    char* exec_filepath = target ? strdup(target) : strdup("a.out");

    pid_t ld_pid = fork();
    if (ld_pid == -1)
    {
        free(exec_filepath);
        errorf("failed to spawn linker process\n");
        return NULL;
    }

    if (ld_pid == 0)
    {
        if (!opts.gflag)
        {
            char** libraries = find_libraries();

            char** argv = calloc(object_count + NO_LIBRARIES + 4, sizeof(char*));
            argv[0] = "/usr/bin/x86_64-linux-gnu-ld";
            for (size_t i = 0; i < object_count; ++i)
                argv[i + 1] = object_files[i];
            for (size_t i = 0; i < NO_LIBRARIES; ++i)
            {
                if (!libraries[i])
                {
                    delete_array((void**) libraries, NO_LIBRARIES);
                    free(exec_filepath);
                    free(argv);
                    errorf("could not locate a required library: %s\n", LIBRARIES[i]);
                    exit(EXIT_FAILURE);
                }
                argv[1 + i + object_count] = libraries[i];
            }
            argv[1 + object_count + NO_LIBRARIES] = "-o";
            argv[2 + object_count + NO_LIBRARIES] = exec_filepath;
            argv[3 + object_count + NO_LIBRARIES] = NULL;
            int status = execv("/usr/bin/x86_64-linux-gnu-ld", argv);
            if (status == -1)
            {
                delete_array((void**) libraries, NO_LIBRARIES);
                free(exec_filepath);
                free(argv);
                errorf("failed to start linker process\n");
                exit(EXIT_FAILURE);
            }
        }
        else
        {
            char** argv = calloc(object_count + 4, sizeof(char*));
            argv[0] = "/usr/bin/gcc";
            for (size_t i = 0; i < object_count; ++i)
                argv[i + 1] = object_files[i];
            argv[1 + object_count] = "-o";
            argv[2 + object_count] = exec_filepath;
            argv[3 + object_count] = NULL;
            int status = execv("/usr/bin/gcc", argv);
            if (status == -1)
            {
                free(exec_filepath);
                free(argv);
                errorf("failed to start linker process\n");
                exit(EXIT_FAILURE);
            }
        }
    }

    int ld_status = EXIT_FAILURE;
    waitpid(ld_pid, &ld_status, 0);
    if (WEXITSTATUS(ld_status))
    {
        free(exec_filepath);
        return NULL;
    }

    return exec_filepath;
}

bool get_options(int argc, char** argv)
{
    memset(&opts, 0, sizeof(program_options_t));
    for (int c; (c = getopt(argc, argv, "hiPpaxLArcSgo:")) != -1;)
    {
        switch (c)
        {
            case 'h':
                opts.hflag = true;
                break;
            case 'i':
                opts.iflag = true;
                break;
            case 'P':
                opts.ppflag = true;
                break;
            case 'p':
                opts.pflag = true;
                break;
            case 'a':
                opts.aflag = true;
                break;
            case 'x':
                opts.xflag = true;
                break;
            case 'L':
                opts.llflag = true;
                break;
            case 'A':
                opts.aaflag = true;
                break;
            case 'r':
                opts.rflag = true;
                break;
            case 'c':
                opts.cflag = true;
                break;
            case 'S':
                opts.ssflag = true;
                break;
            case 'o':
                opts.oflag = optarg;
                break;
            case 'g':
                opts.gflag = true;
                break;
            case '?':
            default:
            {
                errorf("unknown option specified: -%c\n", c);
                return false;
            }
        }
    }
    return true;
}

int handle_ss_flag(int argc, char** argv)
{
    if (opts.oflag && argc - optind > 1)
    {
        errorf("the -o flag can only be used with the -S flag with one file is given as input\n");
        return EXIT_FAILURE;
    }
    for (int i = optind; i < argc; ++i)
    {
        char* created = opts.oflag ? strdup(opts.oflag) : replace_extension(argv[i], ".s");
        char* asm_filepath = compile(argv[i], created);
        free(created);
        if (!asm_filepath)
            return EXIT_FAILURE;
        free(asm_filepath);
    }
    return EXIT_SUCCESS;
}

int handle_c_flag(int argc, char** argv)
{
    if (opts.oflag && argc - optind > 1)
    {
        errorf("the -o flag can only be used with the -c flag with one file is given as input\n");
        return EXIT_FAILURE;
    }
    for (int i = optind; i < argc; ++i)
    {
        char* created = opts.oflag ? strdup(opts.oflag) : replace_extension(argv[i], ".o");
        char* obj_filepath = assemble(argv[i], created);
        free(created);
        if (!obj_filepath)
            return EXIT_FAILURE;
        free(obj_filepath);
    }
    return EXIT_SUCCESS;
}

static int clean_exit(int code)
{
    return code;
}

int main(int argc, char** argv)
{
    PROGRAM_NAME = argv[0];
    srand(time(NULL));
    if (argc <= 1)
    {
        errorf("no input files\n");
        return clean_exit(EXIT_FAILURE);
    }

    if (!get_options(argc, argv))
        return clean_exit(EXIT_FAILURE);
    
    if (opts.hflag)
        return usage();
    
    if (opts.ssflag)
        return handle_ss_flag(argc, argv);
    
    if (opts.cflag)
        return handle_c_flag(argc, argv);
    
    size_t object_count = argc - optind;
    char** objects = calloc(object_count, sizeof(char*));
    for (int i = optind; i < argc; ++i)
    {
        char* filepath = argv[i];
        char* obj_filepath = NULL;
        if (ends_with(filepath, ".c"))
            obj_filepath = assemble(filepath, NULL);
        else if (ends_with(filepath, ".s"))
            obj_filepath = invoke_assembler(filepath, NULL);
        else if (ends_with(filepath, ".o"))
            obj_filepath = strdup(filepath);
        else
        {
            delete_array((void**) objects, object_count);
            errorf("file '%s' has an unexpected extension. expected '.c', '.s', or '.o' (C source files, assembly files, or object files)\n");
            return clean_exit(EXIT_FAILURE);
        }
        if (obj_filepath == NULL)
        {
            delete_array((void**) objects, object_count);
            return clean_exit(EXIT_FAILURE);
        }
        objects[i - optind] = obj_filepath;
    }

    char* exec_filepath = linker(objects, object_count, opts.oflag);

    for (size_t i = 0; i < object_count; ++i)
    {
        if (ends_with(argv[i + optind], ".o"))
            continue;
        remove(objects[i]);
    }

    delete_array((void**) objects, object_count);

    if (!exec_filepath)
    {
        errorf("linker has failed to produce an executable\n");
        return clean_exit(EXIT_FAILURE);
    }

    free(exec_filepath);
    return clean_exit(EXIT_SUCCESS);
}
