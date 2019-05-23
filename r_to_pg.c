/*
 * PL/R - PostgreSQL support for R as a
 *	      procedural language (PL)
 *
 * Copyright (c) 2003-2015 by Joseph E. Conway
 *               2016-2019 by plr contributors
 * ALL RIGHTS RESERVED
 * 
 * Joe Conway <mail@joeconway.com>
 * 
 * Based on pltcl by Jan Wieck
 * and inspired by REmbeddedPostgres by
 * Duncan Temple Lang <duncan@research.bell-labs.com>
 * http://www.omegahat.org/RSPostgres/
 *
 * License: GPL version 2 or newer. http://www.gnu.org/copyleft/gpl.html
 * 
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *
 * plr.c - Language handler and support functions
 */

#include "plr.h"

extern char *last_R_error_msg;

/* Local mapping functions accessible only through get_get_datum factory */
static Datum altintsxp_get_int2(plr_result_entry *e, int idx, bool *isnull);
static Datum intsxp_get_int2(plr_result_entry *e, int idx, bool *isnull);
static Datum altintsxp_get_int4(plr_result_entry *e, int idx, bool *isnull);
static Datum intsxp_get_int4(plr_result_entry *e, int idx, bool *isnull);
//static Datum altrealsxp_get_int8(plr_result_entry *e, int idx, bool *isnull);
static Datum realsxp_get_int8(plr_result_entry *e, int idx, bool *isnull);
//static Datum altrealsxp_get_float4(plr_result_entry *e, int idx, bool *isnull);
static Datum realsxp_get_float4(plr_result_entry *e, int idx, bool *isnull);
static Datum altrealsxp_get_float8(plr_result_entry *e, int idx, bool *isnull);
static Datum realsxp_get_float8(plr_result_entry *e, int idx, bool *isnull);
static Datum realsxp_get_numeric(plr_result_entry *e, int idx, bool *isnull);
static Datum get_bytea(plr_result_entry *e, int idx, bool *isnull);
static Datum get_scalar_datum_through_text(plr_result_entry *e, int idx, bool *isnull);


static Datum
altintsxp_get_int2(plr_result_entry *e, int idx, bool *isnull)
{
	const int el = INTEGER_ELT(e->rval, idx);
	*isnull = NA_INTEGER == el;
	return Int16GetDatum((int16)el);
}

static Datum
intsxp_get_int2(plr_result_entry *e, int idx, bool *isnull)
{
	*isnull = NA_INTEGER == ((int*)e->data_ptr)[idx];
	return Int16GetDatum((int16)(((int*)e->data_ptr)[idx]));
}

static Datum
altintsxp_get_int4(plr_result_entry *e, int idx, bool *isnull)
{
	const int el = INTEGER_ELT(e->rval, idx);
	*isnull = NA_INTEGER == el;
	return Int32GetDatum(el);
}

static Datum
intsxp_get_int4(plr_result_entry *e, int idx, bool *isnull)
{
	*isnull = NA_INTEGER == ((int*)e->data_ptr)[idx];
	return Int32GetDatum(((int*)e->data_ptr)[idx]);
}

static Datum
realsxp_get_float4(plr_result_entry *e, int idx, bool *isnull)
{
	const double el = REAL_ELT(e->rval, idx);
	*isnull = ISNA(el);
	return Float4GetDatum((float4)el);
}

static Datum
altrealsxp_get_float8(plr_result_entry *e, int idx, bool *isnull)
{
	const double el = REAL_ELT(e->rval, idx);
	*isnull = ISNA(el);
	return Float8GetDatum(el);
}

static Datum
realsxp_get_float8(plr_result_entry *e, int idx, bool *isnull)
{
	*isnull = ISNA(((double*)e->data_ptr)[idx]);
	return Float8GetDatum(((double*)e->data_ptr)[idx]);
}

static Datum
realsxp_get_int8(plr_result_entry *e, int idx, bool *isnull)
{
	const double el = REAL_ELT(e->rval, idx);
	*isnull = ISNA(el);
	return Int64GetDatum((int64)el);
}

static Datum
realsxp_get_numeric(plr_result_entry *e, int idx, bool *isnull)
{
	const double el = REAL_ELT(e->rval, idx);
	*isnull = ISNA(el);
	return DirectFunctionCall1(float8_numeric, Float8GetDatum((double)el));
}

static Datum
get_bytea(plr_result_entry *e, int idx, bool *isnull)
{
	SEXP		obj;
	int			len, rsize, status;
	bytea	   *result;
	char	   *rptr;

	PROTECT(obj = R_tryEval(lang3(install("serialize"), e->rval, R_NilValue), R_GlobalEnv, &status));
	if (status != 0)
	{
		if (last_R_error_msg)
			ereport(ERROR,
			(errcode(ERRCODE_DATA_EXCEPTION),
			 errmsg("R interpreter expression evaluation error"),
			 errdetail("%s", last_R_error_msg)));
		else
			ereport(ERROR,
			(errcode(ERRCODE_DATA_EXCEPTION),
			 errmsg("R interpreter expression evaluation error"),
			 errdetail("R expression evaluation error caught in \"serialize\".")));
	}
	len = LENGTH(obj);

	rsize = VARHDRSZ + len;
	result = (bytea *)palloc(rsize);
	SET_VARSIZE(result, rsize);
	rptr = VARDATA(result);
	memcpy(rptr, (char *)RAW(obj), rsize - VARHDRSZ);

	UNPROTECT(1);

	*isnull = false;
	return PointerGetDatum(result);
}

static Datum
get_scalar_datum_through_text(plr_result_entry *e, int idx, bool *isnull)
{
	SEXP		obj;
	const char *value;

	if (TYPEOF(e->rval) == STRSXP)
		obj = e->rval;
	else
	{
		if (likely(!isFactor(e->rval)))
		{
			/*
			 * ExtractSubset is hidden and is accidentally exposed on Windows. Should not rely on it.
			 * Let's keep it here in case it gets exported.
			 */
#if 0
			obj = coerce_to_char(length(e->rval) > 1 ? ExtractSubset(e->rval, ScalarInteger(idx + 1), NULL) : rval);
#else
			if (length(e->rval) > 1)
			{
				int status;
				obj = coerce_to_char(R_tryEval(lang3(R_Bracket2Symbol, e->rval, ScalarInteger(idx + 1)), R_GlobalEnv, &status));
				if (unlikely(status))
					elog(ERROR, "Failed to get subscript");
			}
			else
				obj = coerce_to_char(e->rval);
#endif
			idx = 0;
		}
		else
		{
			obj = GET_LEVELS(e->rval);
			idx = INTEGER_ELT(e->rval, idx) - 1;
		}
	}

	/*
	 * object coerced to absent string
	 */
	if (STRING_ELT(obj, idx) == NA_STRING)
	{
		*isnull = true;
		return (Datum)0;
	}
	obj = STRING_ELT(obj, idx);
	if (TYPEOF(obj) == CHARSXP)
	{
		value = CHAR(obj);
	}
	else
	{
		ereport(ERROR,
			(errcode(ERRCODE_DATA_EXCEPTION),
			 errmsg("R interpreter expression evaluation error"),
			 errdetail("return type cannot be coerced to char")));
	}

	if (value != NULL)
	{
		*isnull = false;
		return FunctionCall3(&e->elem_in_func,
							 CStringGetDatum(value),
							 ObjectIdGetDatum(0),
							 Int32GetDatum(-1));
	}

	*isnull = true;
	return (Datum)0;
}

void
get_get_datum(SEXP rval, plr_result_entry *e)
{
	const int sxp_type = TYPEOF(rval);
	const bool is_std = !ALTREP(rval);
	e->rval = rval;

	switch (e->elem_typid)
	{
		case BOOLOID:
		case INT4OID:
			switch (sxp_type)
			{
				case LGLSXP:
				case INTSXP:
					if (is_std)
					{
						e->data_ptr = STDVEC_DATAPTR(rval);
						e->get_datum = intsxp_get_int4;
						return;
					}

					e->get_datum = altintsxp_get_int4;
					return;
			};
			break;
		case INT8OID:
			switch (sxp_type)
			{
				case REALSXP:
					e->get_datum = realsxp_get_int8;
					return;
			}
		case INT2OID:
			switch (sxp_type)
			{
				case INTSXP:
					if (is_std)
					{
						e->data_ptr = STDVEC_DATAPTR(rval);
						e->get_datum = intsxp_get_int2;
						return;
					}

					e->get_datum = altintsxp_get_int2;
					return;
			}
		case FLOAT4OID:
			switch (sxp_type)
			{
				case REALSXP:
					e->get_datum = realsxp_get_float4;
					return;
			}
			break;
		case FLOAT8OID:
			switch (sxp_type)
			{
				case REALSXP:
					if (is_std)
					{
						e->data_ptr = STDVEC_DATAPTR(rval);
						e->get_datum = realsxp_get_float8;
						return;
					}

					e->get_datum = altrealsxp_get_float8;
					return;
			}
			break;
		case NUMERICOID:
			switch (sxp_type)
			{
				case REALSXP:
					e->get_datum = realsxp_get_numeric;
					return;
			}
		case BYTEAOID:
			e->get_datum = get_bytea;
			return;
	};

	e->get_datum = get_scalar_datum_through_text;
}
