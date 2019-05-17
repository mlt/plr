/*
 * PL/R - PostgreSQL support for R as a
 *	      procedural language (PL)
 *
 * Copyright (c) 2003-2015 by Joseph E. Conway
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

Datum
altintsxp_get_int2(SEXP rval, int idx, FmgrInfo *result_in_func, bool *isnull, void *data_ptr)
{
	const int el = ALTINTEGER_ELT(rval, idx);
	*isnull = NA_INTEGER == el;
	return Int16GetDatum((int16)el);
}

Datum
intsxp_get_int2(SEXP rval, int idx, FmgrInfo *result_in_func, bool *isnull, void *data_ptr)
{
	*isnull = NA_INTEGER == ((int*)data_ptr)[idx];
	return Int16GetDatum((int16)(((int*)data_ptr)[idx]));
}

Datum
altintsxp_get_int4(SEXP rval, int idx, FmgrInfo *result_in_func, bool *isnull, void *data_ptr)
{
	const int el = ALTINTEGER_ELT(rval, idx);
	*isnull = NA_INTEGER == el;
	return Int32GetDatum(el);
}

Datum
intsxp_get_int4(SEXP rval, int idx, FmgrInfo *result_in_func, bool *isnull, void *data_ptr)
{
	*isnull = NA_INTEGER == ((int*)data_ptr)[idx];
	return Int32GetDatum(((int*)data_ptr)[idx]);
}

Datum
realsxp_get_float4(SEXP rval, int idx, FmgrInfo *result_in_func, bool *isnull, void *data_ptr)
{
	const double el = REAL_ELT(rval, idx);
	*isnull = ISNA(el);
	return Float4GetDatum((float4)el);
}

Datum
altrealsxp_get_float8(SEXP rval, int idx, FmgrInfo *result_in_func, bool *isnull, void *data_ptr)
{
	const double el = ALTREAL_ELT(rval, idx);
	*isnull = ISNA(el);
	return Float8GetDatum(el);
}

Datum
realsxp_get_float8(SEXP rval, int idx, FmgrInfo *result_in_func, bool *isnull, void *data_ptr)
{
	*isnull = ISNA(((double*)data_ptr)[idx]);
	return Float8GetDatum(((double*)data_ptr)[idx]);
}

Datum
realsxp_get_int8(SEXP rval, int idx, FmgrInfo *result_in_func, bool *isnull, void *data_ptr)
{
	const double el = REAL_ELT(rval, idx);
	*isnull = ISNA(el);
	return Int64GetDatum((int64)el);
}

Datum
realsxp_get_numeric(SEXP rval, int idx, FmgrInfo *result_in_func, bool *isnull, void *data_ptr)
{
	const double el = REAL_ELT(rval, idx);
	*isnull = ISNA(el);
	return DirectFunctionCall1(float8_numeric, Float8GetDatum((double)el));
}

Datum
get_bytea(SEXP rval, int idx, FmgrInfo *result_in_func, bool *isnull, void *data_ptr)
{
	SEXP		obj;
	int			len, rsize, status;
	bytea	   *result;
	char	   *rptr;

	PROTECT(obj = R_tryEval(lang3(install("serialize"), rval, R_NilValue), R_GlobalEnv, &status));
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

static inline Datum
get_scalar_datum_through_text(SEXP rval, int idx, FmgrInfo *result_in_func, bool *isnull, void *data_ptr)
{
	SEXP		obj;
	const char *value;

	if (TYPEOF(rval) == STRSXP)
		obj = rval;
	else
	{
		if (likely(!isFactor(rval)))
		{
			/*
			 * ExtractSubset is hidden and is accidentally exposed on Windows. Should not rely on it.
			 * Let's keep it here in case it gets exported.
			 */
#if 0
			obj = coerce_to_char(length(rval) > 1 ? ExtractSubset(rval, ScalarInteger(idx + 1), NULL) : rval);
#else
			if (length(rval) > 1)
			{
				int status;
				obj = coerce_to_char(R_tryEval(lang3(R_Bracket2Symbol, rval, ScalarInteger(idx + 1)), R_GlobalEnv, &status));
				if (unlikely(status))
					elog(ERROR, "Failed to get subscript");
			}
			else
				obj = coerce_to_char(rval);
#endif
			idx = 0;
		}
		else
		{
			obj = GET_LEVELS(rval);
			idx = INTEGER_ELT(rval, idx) - 1;
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
		return FunctionCall3(result_in_func,
							 CStringGetDatum(value),
							 ObjectIdGetDatum(0),
							 Int32GetDatum(-1));
	}

	*isnull = true;
	return (Datum)0;
}

get_datum_type
get_get_datum(SEXP rval, Oid typid, void** data_ptr)
{
	const int sxp_type = TYPEOF(rval);
	const bool is_std = !ALTREP(rval);

	switch (typid)
	{
		case BOOLOID:
		case INT4OID:
			switch (sxp_type)
			{
				case LGLSXP:
				case INTSXP:
					if (is_std)
					{
						*data_ptr = STDVEC_DATAPTR(rval);
						return intsxp_get_int4;
					}
					else
						return altintsxp_get_int4;
			};
			break;
		case INT8OID:
			switch (sxp_type)
			{
				case REALSXP:
					return realsxp_get_int8;
			}
		case INT2OID:
			switch (sxp_type)
			{
				case INTSXP:
					if (is_std)
					{
						*data_ptr = STDVEC_DATAPTR(rval);
						return intsxp_get_int2;
					}
					else
						return altintsxp_get_int2;
			}
		case FLOAT4OID:
			switch (sxp_type)
			{
				case REALSXP:
					return realsxp_get_float4;
			}
			break;
		case FLOAT8OID:
			switch (sxp_type)
			{
				case REALSXP:
					if (is_std)
					{
						*data_ptr = STDVEC_DATAPTR(rval);
						return realsxp_get_float8;
					}
					else
						return altrealsxp_get_float8;
			}
			break;
		case NUMERICOID:
			switch (sxp_type)
			{
				case REALSXP:
					return realsxp_get_numeric;
			}
		case BYTEAOID:
			return get_bytea;
	};

	return get_scalar_datum_through_text;
}
