#ifndef __READ_STATS_FILE__
#define __READ_STATS_FILE__

#include "postgres.h"
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "catalog/pg_statistic.h"
#include "experimental/uthash.h"
#include "utils/elog.h"
#include "utils/palloc.h"
#define STA_NUM 31
#define MAX_LEN 1000

typedef enum QuotesSettings
{
	QUOTES_INCLUDED = 1,
	QUOTES_EXCLUDED = 2,
	REMOVE_ESCAPES = 4
} QuotesSettings;

typedef struct TokenNode
{
	Datum token;
	struct TokenNode *next;
} TokenNode;

typedef struct FloatNode
{
	float4 num;
	struct FloatNode *next;
} FloatNode;






struct attrs
{
	// tp be used for column statistics
	Oid starelid;
	int tupattnum;
	int staatnum;
	char stainherit;
	float4 stanullfrac;
	int32 stawidth;
	float4 stadistinct;
	int16 stakind[STATISTIC_NUM_SLOTS];
	Oid staop[STATISTIC_NUM_SLOTS];
	long int stacoll[STATISTIC_NUM_SLOTS];
	int numnumbers[STATISTIC_NUM_SLOTS];
	int numvalues[STATISTIC_NUM_SLOTS];
	FloatNode *stanumbers[STATISTIC_NUM_SLOTS];
	TokenNode *stavalues[STATISTIC_NUM_SLOTS];

	// to be used for relation statistics
	char relname[64];
	float4 reltuples;
	int relpages;
	int relallvisible;

	
};

void delete_float_list(FloatNode *node)
{

    if(node == NULL){
        return;
    }
    
    delete_float_list(node->next);
   
    
    
    pfree(node);

}
void delete_token_list(TokenNode *node)
{
    if(node == NULL){
        return;
    }
    
    delete_token_list(node->next);
    
    
    pfree((char *)node->token);
    pfree(node);
}

typedef struct attrs attrs;


typedef struct vector
{
	attrs* sarray[MAX_LEN];
	attrs** darray;
	attrs** arrptr;
	int len;
	int capacity;
} vector;

static void init_vector(vector *v)
{
	v->arrptr = v->sarray;
	v->darray = NULL;
	v->len = 0;
	v->capacity = MAX_LEN;
	memset(v->arrptr, 0, MAX_LEN * sizeof(attrs *));
}

static void add_element(vector *v, attrs* el)
{
	if(v->arrptr == v->sarray){
		if(v->len < (v->capacity - 1)){
			v->arrptr[v->len++] = el;	
		}else{
			v->darray = palloc(v->len * 2 * sizeof(attrs *));
			memset(v->darray, 0, v->len * 2 * sizeof(attrs *));
			memcpy(v->darray, v->sarray, v->len * sizeof(attrs *));
			v->capacity = v->len * 2;
			v->arrptr = v->darray;
			add_element(v, el);
			
		}
	}else{
		if(v->len < (v->capacity - 1)){
			v->arrptr[v->len++] = el;
		}else{
			char *p = realloc(v->arrptr, v->len * 2 * sizeof(attrs *));
			v->arrptr[v->len++] = el;
			
			v->capacity = v->len * 2;

		}
	}
}

static void free_vector(vector *v)
{
	if(v->arrptr == v->darray){
		pfree(v->darray);
		v->darray = NULL;
		v->arrptr = NULL;
	}
}
vector *att_table = NULL;
vector *att_table_rel = NULL;
static int
readline(FILE *fptr, char **output)
{
	// printf("inseide readline\n");
	ereport(LOG, (errmsg("Sairam: Entered readline")));
	char c;
	int len = 500;
	*output = (char *) palloc(len * sizeof(char));
	memset(*output, 0, len * sizeof(char));
	char *out = *output;

	int l = 0;
	while ((c = fgetc(fptr)) != '\n' && c != EOF)
	{
		if (l == (len - 1))
		{
			char *tmp = (char *) palloc(len * 2 * sizeof(char));
			memset(tmp, 0, len * 2 * sizeof(char));
			memcpy(tmp, *output, len);
			out = tmp + (len - 1);
			len = len * 2;
			pfree(*output);
			*output = tmp;
		}
		*out = c;
		// printf("%c", *out);
		// ereport(INFO, (errmsg("Sairam: %c", *out)));
		out++;
		l++;
	}
	*out = '\0';
	// printf("Read line successfully\n");
	ereport(LOG, (errmsg("Sairam: Finished readline")));
	return strlen(*output);
}

static char *
handle_quoted_string(char *p, char **token, QuotesSettings setting)
{
	char *tokptr = *token;
	if (*p == '"')
	{
		if ((setting & QUOTES_INCLUDED) == QUOTES_INCLUDED)
		{
			*tokptr = *p;
			tokptr++;
		}

		p++;
		while (*p != '"')
		{
			if (*p == '\\' && *(p + 1) == '\\')
			{
				if ((setting & REMOVE_ESCAPES) != REMOVE_ESCAPES)
				{
					*tokptr = *p;
					tokptr++;
				}
				p++;
				if ((setting & REMOVE_ESCAPES) != REMOVE_ESCAPES)
				{
					*tokptr = *p;
					tokptr++;
				}
				p++;
				*tokptr = *p;
				tokptr++;
				p++;
			}
			else
			{
				*tokptr = *p;
				tokptr++;
				p++;
			}
		}
		if ((setting & QUOTES_INCLUDED) == QUOTES_INCLUDED)
		{
			*tokptr = *p;
			tokptr++;
		}
		p++;
	}

	*token = tokptr;
	return p;
}

static char *
skip_white_space(char *p)
{
	while (*p && isspace(*p))
		p++;
	return p;
}

static char *
parse_csv(char *p, char *token)
{
	// printf("parse csv started\n");
	p = skip_white_space(p);
	if (*p == '"')
	{
		p = handle_quoted_string(
			p, &token, (QuotesSettings) (QUOTES_EXCLUDED | REMOVE_ESCAPES));
		*token = '\0';
		while (*p && *p != ',')
			p++;
		if (*p)
			p++;
	}
	else
	{
		while (*p && *p != ',')
		{
			*token = *p;
			token++;
			p++;
		}
		*token = '\0';
		if (*p) // meaning that , exists
			p++;
	}
	// printf("parse_csv successful\n");
	return p;
}
static char *
tokenize(char *p, char *token)
{
	// printf("inside tokenize\n");

	// int len = strlen(p);
	p = skip_white_space(p);
	if (*p == '{')
	{
		// printf("Sairam {}\n");
		p++;
		while (*p)
		{
			if (*p == '"')
				p = handle_quoted_string(p, &token, QUOTES_INCLUDED);
			else
			{
				*token = *p;

				token++;
				p++;
			}
			if (*p == '}')
				break;
		}

		// p == '}' should always be satisfied
		*token = '\0';
		p++;
	}
	else if (!isspace(*p))
	{
		// printf("Sairam\n");

		while (*p && !isspace(*p))
		{
			*token = *p;
			token++;
			p++;
		}
		*token = '\0';
	}
	// while(**p && isspace(**p)) (*p)++;
	// printf("finished tokenize\n");
	return p;
}

static void
set_stats(attrs *stats, char *token_list[], int len)
{
	// printf("setstats started\n");
	char **tl = token_list;
	stats->starelid = atol(tl[0]);
	stats->staatnum = atoi(tl[1]);
	ereport(LOG, (errmsg("Sairam: Entered set_stats(relid: %lu, staatnum: %d)", stats->starelid, stats->staatnum)));
	
	// printf("Sairam %s\n", tl[0]);
	stats->stainherit = tl[2][0];
	stats->stanullfrac = atof(tl[3]);
	stats->stawidth = atoi(tl[4]);
	stats->stadistinct = atof(tl[5]);
	for (int i = 0; i < STATISTIC_NUM_SLOTS; i++)
	{
		stats->stakind[i] = atol(tl[6 + i]);
	}
	for (int i = 0; i < STATISTIC_NUM_SLOTS; i++)
	{
		stats->staop[i] = atol(tl[11 + i]);
	}
	// printf("ops done\n");
	if (len == 31)
	{
		for (int i = 0; i < STATISTIC_NUM_SLOTS; i++)
		{
			stats->stacoll[i] = atol(tl[16 + i]);
		}
		for (int i = 0; i < STATISTIC_NUM_SLOTS; i++)
		{
			stats->stanumbers[i] = (FloatNode *) palloc(sizeof(FloatNode));
			// printf("TL %s\n", tl[21 + i]);
			if (strcmp(tl[21 + i], "\\N") == 0)
			{
				// printf("NULL\n");
				stats->stanumbers[i]->next = NULL;
				stats->numnumbers[i] = 0;
				continue;
			}
			int slen = strlen(tl[21 + i]) + 1;
			char *val = (char *) palloc(slen * sizeof(char)); // unnecessary
															  // space used
			char *p = tl[21 + i];
			FloatNode *ptr = stats->stanumbers[i];
			stats->numnumbers[i] = 0;
			while (*p)
			{
				memset(val, 0, slen * sizeof(char));
				p = parse_csv(p, val);

				ptr->next = (FloatNode *) palloc(sizeof(FloatNode));
				ptr = ptr->next;

				ptr->num = atof(val);
				stats->numnumbers[i]++;
				// printf("CSVC - %f\n", ptr->num);
			}
			ptr->next = NULL;
			pfree(val);
		}
		for (int i = 0; i < STATISTIC_NUM_SLOTS; i++)
		{
			// printf("for loop started\n");
			stats->stavalues[i] = (TokenNode *) palloc(sizeof(TokenNode));
			stats->stavalues[i]->token = (Datum)palloc(1 * sizeof(char));
			if (strcmp(tl[26 + i], "\\N") == 0)
			{
				stats->stavalues[i]->next = NULL;
				stats->numvalues[i] = 0;
				continue;
			}
			char *p = tl[26 + i];
			int slen = strlen(tl[26 + i]) + 1;
			char *val = (char *) palloc(slen * sizeof(char)); // unnecessary
															  // space used
			stats->stavalues[i]->next = NULL;
			TokenNode *ptr = stats->stavalues[i];
			stats->numvalues[i] = 0;
			while (*p)
			{
				// printf("while loop started\n");
				memset(val, 0, slen * sizeof(char));
				p = parse_csv(p, val);
				// printf("CSV - %s\n", val);
				ptr->next = (TokenNode *) palloc(sizeof(TokenNode));
				ptr = ptr->next;
				int val_len = strlen(val) + 1;
				ptr->token = (Datum) palloc(val_len * sizeof(char));
				strncpy((char *) ptr->token, val, val_len);
				stats->numvalues[i]++;
				// printf("t: %s \n", (char *) ptr->token);
			}
			ptr->next = NULL;
			pfree(val);
		}
	}
	else
	{
		for (int i = 0; i < STATISTIC_NUM_SLOTS; i++)
		{
			stats->stanumbers[i] = (FloatNode *) palloc(sizeof(FloatNode));
			// printf("TL %s\n", tl[16 + i]);
			if (strcmp(tl[16 + i], "\\N") == 0)
			{
				// printf("NULL\n");
				stats->stanumbers[i]->next = NULL;
				stats->numnumbers[i] = 0;
				continue;
			}
			int slen = strlen(tl[16 + i]) + 1;
			char *val = (char *) palloc(slen * sizeof(char)); // unnecessary
															  // space used
			char *p = tl[16 + i];
			FloatNode *ptr = stats->stanumbers[i];
			stats->numnumbers[i] = 0;
			// printf("csvline - %s\n", tl[16 + i]);
			while (*p)
			{
				memset(val, 0, slen * sizeof(char));
				p = parse_csv(p, val);

				ptr->next = (FloatNode *) palloc(sizeof(FloatNode));
				ptr = ptr->next;
				ptr->num = atof(val);
				stats->numnumbers[i]++;
				// printf("CSVC - %s %f\n", val, ptr->num);
			}
			ptr->next = NULL;
			pfree(val);
		}

		for (int i = 0; i < STATISTIC_NUM_SLOTS; i++)
		{
			// printf("for loop started\n");
			stats->stavalues[i] = (TokenNode *) palloc(sizeof(TokenNode));
			stats->stavalues[i]->token = (Datum)palloc(1 * sizeof(char));
			if (strcmp(tl[21 + i], "\\N") == 0)
			{
				stats->stavalues[i]->next = NULL;
				stats->numvalues[i] = 0;
				continue;
			}
			char *p = tl[21 + i];
			int slen = strlen(tl[21 + i]) + 1;
			char *val = (char *) palloc(slen * sizeof(char)); // unnecessary
															  // space used
			stats->stavalues[i]->next = NULL;
			TokenNode *ptr = stats->stavalues[i];
			stats->numvalues[i] = 0;
			while (*p)
			{
				// printf("while loop started\n");
				memset(val, 0, slen * sizeof(char));
				p = parse_csv(p, val);
				// printf("CSV - %s\n", val);
				ptr->next = (TokenNode *) palloc(sizeof(TokenNode));
				ptr = ptr->next;
				int val_len = strlen(val) + 1;
				ptr->token = (Datum) palloc(val_len * sizeof(char));
				strncpy((char *) ptr->token, val, val_len);
				stats->numvalues[i]++;
				// printf(" %d:: %d %d: %s \n", i + 1, stats->starelid,
				// stats->staatnum, (char *)ptr->token);
			}
			ptr->next = NULL;
			pfree(val);
		}
	}
	ereport(LOG, (errmsg("Sairam: Finished set_stats(relid: %lu)", stats->starelid)));
	// printf("setstats successful\n");
}

static void set_class(attrs *info, char *token_list[], int len)
{
    memset(info->relname, 0, 64);
    memcpy(info->relname, token_list[0], 64);
    info->relpages = atof(token_list[1]);
    info->reltuples = atof(token_list[2]);
    info->relallvisible = atoi(token_list[3]);
}


static void free_token_list(char **token_list, int len)
{
    for(int i = 0; i < len; i++){
        if(token_list[i])
            pfree(token_list[i]);
    }
}

static int
readstatline(FILE *fptr, attrs *stats)
{
	// printf("inside rstatisline\n");
	ereport(LOG, (errmsg("Sairam: Entered readstatline()")));
	char *line;

	int line_length = readline(fptr, &line);

	// printf("Line props: %s %lu\n", line, strlen(line));

	if (line_length == 0){
		pfree(line);
		return line_length;
	}

	char *token = (char *) palloc((line_length + 1) * sizeof(char));
	// printf("palloc done\n");
	char *p = line;
	// char *tmp = line;
	// printf("%c\n", **p);
	// char x = **p;
	// printf("0\n");
	char *token_list[STA_NUM] = {0};
	int len = 0;
	while (*p)
	{
		memset(token, 0, line_length * sizeof(char));
		// printf("1\n");
		p = tokenize(p, token);
		int tok_len = strlen(token) + 1;
		token_list[len] = (char *) palloc(tok_len * sizeof(char));
		strncpy(token_list[len], token, tok_len);
		// printf("token %d - %s\n", len, token);
		len++;
	}

	// for(int i = 0; i < len; i++){
	//     printf("%s\n", token_list[i]);
	// }
	set_stats(stats, token_list, len);
	if(line != NULL)
		pfree(line);
	if(token != NULL)
		pfree(token);
	
	free_token_list(token_list, len);
	token = NULL;
	line = NULL;
	// printf("finished\n");
	ereport(LOG, (errmsg("Sairam: Finished readstatline()")));
	return line_length;
}

static int read_relclass_line(FILE *fptr, attrs *class)
{
    char *line;
    
    int line_length = readline(fptr, &line);
    
    
    // printf("Line props: %s %lu\n", line, strlen(line));
    
    if(line_length == 0){
        pfree(line);
        return line_length;
    }

    char *token = palloc((line_length + 1) * sizeof(char));
    // printf("malloc done\n");
    char *p = line;
    // char *tmp = line;
    // printf("%c\n", **p);
    // char x = **p;
    // printf("0\n");
    char * token_list[STA_NUM] = {0};
    int len = 0;
    while(*p){
        memset(token, 0, line_length * sizeof(char));
        // printf("1\n");
        p = tokenize(p, token);
        int tok_len = strlen(token) + 1;
        token_list[len] = palloc(tok_len * sizeof(char));
        strncpy(token_list[len], token, tok_len);
        // printf("token %d - %s\n", len, token);
        len++;
    }

    for(int i = 0; i < len; i++){
        printf("%s ", token_list[i]);
    }
    putchar('\n');
    set_class(class, token_list, len);
    pfree(line);
    pfree(token);
    free_token_list(token_list, len);
    token = NULL;
    line = NULL;
    // printf("finished\n");
    return line_length;
}


static void free_resources(vector *att_table)
{
	if(!att_table) return;
    for(int i = 0; i < att_table->len; i++){
		for(int j = 0; j < STATISTIC_NUM_SLOTS; j++){
			if(att_table->arrptr[i]->stanumbers[j] != NULL)
            	delete_float_list(att_table->arrptr[i]->stanumbers[j]);
			if(att_table->arrptr[i]->stavalues[j] != NULL)
            	delete_token_list(att_table->arrptr[i]->stavalues[j]);
        }
        pfree(att_table->arrptr[i]);
    }
    free_vector(att_table);
    pfree(att_table);
}

attrs * get_attstruct(Oid relid, int tupattnum)
{
	ereport(LOG, (errmsg("Sairam: Entered get_attstruct() -> %p %d %d", att_table, relid, tupattnum)));
    attrs *out = NULL;
    
    for(int i = 0; i < att_table->len; i++){
        if(att_table->arrptr[i]->starelid == relid && att_table->arrptr[i]->staatnum == tupattnum){
            out = att_table->arrptr[i];
        }
    }
	ereport(LOG, (errmsg("Sairam: Finished get_attstruct()")));
    return out;
}

attrs * get_attstruct_rel(char relname[])
{
	ereport(LOG, (errmsg("Sairam: Entered get_attstruct_rel() -> %p %s", att_table_rel, relname)));
    attrs *out = NULL;
    
    for(int i = 0; i < att_table_rel->len; i++){
        if(strncmp(att_table_rel->arrptr[i]->relname, relname, 64) == 0){
            out = att_table_rel->arrptr[i];
        }
    }
	ereport(LOG, (errmsg("Sairam: Finished get_attstruct_rel()")));
    return out;
}



void initialize_attstructs(char *filename, bool relstats)
{
	ereport(INFO, (errmsg("Sairam: Entered initialize_attstructs()")));
    FILE *fptr = fopen(filename, "r");
    attrs tmp;
    memset(&tmp, 0, sizeof(tmp));
	if(relstats) {
		att_table_rel = palloc(sizeof(vector));
		init_vector(att_table_rel);
		while(read_relclass_line(fptr, &tmp)){
        
            attrs *val = palloc(sizeof(attrs));
            memcpy(val, &tmp, sizeof(attrs));
            add_element(att_table_rel, val);
        
        }
	}else{

		att_table = palloc(sizeof(vector));
		init_vector(att_table);
		while(readstatline(fptr, &tmp)){
			
			attrs *val = palloc(sizeof(attrs));
			memcpy(val, &tmp, sizeof(attrs));
			add_element(att_table, val);
			
		}
	}
	fclose(fptr);
	ereport(INFO, (errmsg("Sairam: Finished initialize_attstructs()")));
    return;
}




void
free_exp_stat_resources()
{
	ereport(INFO, (errmsg("Sairam: free_exp_stat_resources()")));
	free_resources(att_table);
	free_resources(att_table_rel);
	// for(int i = 0; i < att_table->len; i++){
	// 	for(int j = 0; j < STATISTIC_NUM_SLOTS; j++){
	// 		if(att_table->arrptr[i]->stanumbers[j] != NULL)
    //         	delete_float_list(att_table->arrptr[i]->stanumbers[j]);
	// 		if(att_table->arrptr[i]->stavalues[j] != NULL)
	//             delete_token_list(att_table->arrptr[i]->stavalues[j]);
    //     }
    //     pfree(att_table->arrptr[i]);
    // }
    // free_vector(att_table);
    // pfree(att_table);
	att_table = NULL;
	att_table_rel = NULL;
	ereport(INFO, (errmsg("Sairam: Finished free_exp_stat_resources()")));
}

bool is_rel_att_table()
{
	return (att_table_rel != NULL);
}

bool is_att_table()
{
	return (att_table != NULL);
}
#endif