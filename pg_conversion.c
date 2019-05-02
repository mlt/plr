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
 * pg_conversion.c - functions for converting arguments from pg types to
 *                   R types, and for converting return values from R types
 *                   to pg types
 */
#include "plr.h"

static void pg_get_one_r(char *value, Oid arg_out_fn_oid, SEXP *obj,
																int elnum);
static SEXP get_r_vector(Oid typtype, int64 numels);
static Datum get_trigger_tuple(SEXP rval, FunctionCallInfo fcinfo, bool *isnull);
static Datum get_tuplestore(SEXP rval, plr_result *result, FunctionCallInfo fcinfo);
static Datum get_array_datum(SEXP rval, plr_result *result, int col);
static inline Datum get_scalar_datum_through_text(SEXP rval, int idx, FmgrInfo *result_in_func, bool *isnull);
static Datum get_frame_array_datum(SEXP rval, plr_result *result, int col);
static Datum get_md_array_datum(SEXP rval, plr_result *result, int col);
static void get_tuplestore_imp(SEXP rval, plr_result *result, TupleDesc tupdesc, Tuplestorestate *tupstore);
static SEXP coerce_to_char(SEXP rval);
static Datum r_get_tuple(SEXP rval, plr_result *result, FunctionCallInfo fcinfo);

extern char *last_R_error_msg;

/*
 * given a scalar pg value, convert to a one row R vector
 */
SEXP
pg_scalar_get_r(Datum dvalue, Oid arg_typid, FmgrInfo arg_out_func)
{
	SEXP		result;

	/* add our value to it */
	if (arg_typid != BYTEAOID)
	{
		char	   *value;

		value = DatumGetCString(FunctionCall3(&arg_out_func,
											  dvalue,
								 			  (Datum) 0,
											  Int32GetDatum(-1)));

		/* get new vector of the appropriate type, length 1 */
		PROTECT(result = get_r_vector(arg_typid, 1));
		pg_get_one_r(value, arg_typid, &result, 0);
		UNPROTECT(1);
	}
	else
	{
		SEXP 	s, t, obj;
		int		status;
		Datum	dt_dvalue =  PointerGetDatum(PG_DETOAST_DATUM(dvalue));
		int		bsize = VARSIZE((bytea *) dt_dvalue);

		PROTECT(obj = get_r_vector(arg_typid, bsize));
		memcpy((char *) RAW(obj),
			   VARDATA((bytea *) dt_dvalue),
			   bsize);

		/*
		 * Need to construct a call to
		 * unserialize(rval)
		 */
		PROTECT(t = s = allocList(2));
		SET_TYPEOF(s, LANGSXP);
		SETCAR(t, install("unserialize"));
		t = CDR(t);
		SETCAR(t, obj);

		PROTECT(result = R_tryEval(s, R_GlobalEnv, &status));
		if(status != 0)
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
						 errdetail("R expression evaluation error caught in \"unserialize\".")));
		}

		UNPROTECT(3);
	}

	return result;
}


/*
 * Given an array pg value, convert to a multi-row R vector.
 */
SEXP
pg_array_get_r(Datum dvalue, FmgrInfo out_func, int typlen, bool typbyval, char typalign)
{
	/*
	 * Loop through and convert each scalar value.
	 * Use the converted values to build an R vector.
	 */
	SEXP		result;
	ArrayType  *v;
	Oid			element_type;
	int			i, j, k,
				nitems,
				nr = 1,
				nc = 1,
				nz = 1,
				ndim,
			   *dim;
	int			elem_idx = 0;
	Datum	   *elem_values;
	bool	   *elem_nulls;
	bool		fast_track_type;

	/* short-circuit for NULL datums */
	if (dvalue == (Datum) NULL)
		return R_NilValue;

	v = DatumGetArrayTypeP(dvalue);
	ndim = ARR_NDIM(v);
	element_type = ARR_ELEMTYPE(v);
	dim = ARR_DIMS(v);
	nitems = ArrayGetNItems(ARR_NDIM(v), ARR_DIMS(v));

	switch (element_type)
	{
		case INT4OID:
		case FLOAT8OID:
			fast_track_type = true;
			break;
		default:
			fast_track_type = false;
	}

	/*
	 * Special case for pass-by-value data types, if the following conditions are met:
	 * 		designated fast_track_type
	 * 		no NULL elements
	 * 		1 dimensional array only
	 * 		at least one element
	 */
	if (fast_track_type &&
		 typbyval &&
		 !ARR_HASNULL(v) &&
		 (ndim == 1) &&
		 (nitems > 0))
	{
		char	   *p = ARR_DATA_PTR(v);

		/* get new vector of the appropriate type and length */
		PROTECT(result = get_r_vector(element_type, nitems));

		/* keep this in sync with switch above -- fast_track_type only */
		switch (element_type)
		{
			case INT4OID:
				Assert(sizeof(int) == 4);
				memcpy(INTEGER_DATA(result), p, nitems * sizeof(int));
				break;
			case FLOAT8OID:
				Assert(sizeof(double) == 8);
				memcpy(NUMERIC_DATA(result), p, nitems * sizeof(double));
				break;
			default:
				/* Everything else is error */
				ereport(ERROR,
						(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
						 errmsg("direct array passthrough attempted for unsupported type")));
		}

		if (ndim > 1)
		{
			SEXP	matrix_dims;

			/* attach dimensions */
			PROTECT(matrix_dims = allocVector(INTSXP, ndim));
			for (i = 0; i < ndim; i++)
				INTEGER_DATA(matrix_dims)[i] = dim[i];

			setAttrib(result, R_DimSymbol, matrix_dims);
			UNPROTECT(1);
		}

		UNPROTECT(1);	/* result */
	}
	else
	{
		deconstruct_array(v, element_type,
						  typlen, typbyval, typalign,
						  &elem_values, &elem_nulls, &nitems);

		/* array is empty */
		if (nitems == 0)
		{
			PROTECT(result = get_r_vector(element_type, nitems));
			UNPROTECT(1);

			return result;
		}

		if (ndim == 1)
			nr = nitems;
		else if (ndim == 2)
		{
			nr = dim[0];
			nc = dim[1];
		}
		else if (ndim == 3)
		{
			nr = dim[0];
			nc = dim[1];
			nz = dim[2];
		}
		else
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("greater than 3-dimensional arrays are not yet supported")));

		/* get new vector of the appropriate type and length */
		PROTECT(result = get_r_vector(element_type, nitems));

		/* Convert all values to their R form and build the vector */
		for (i = 0; i < nr; i++)
		{
			for (j = 0; j < nc; j++)
			{
				for (k = 0; k < nz; k++)
				{
					char	   *value;
					Datum		itemvalue;
					bool		isnull;
					int			idx = (k * nr * nc) + (j * nr) + i;

					isnull = elem_nulls[elem_idx];
					itemvalue = elem_values[elem_idx++];

					if (!isnull)
					{
						value = DatumGetCString(FunctionCall3(&out_func,
															  itemvalue,
															  (Datum) 0,
															  Int32GetDatum(-1)));
					}
					else
						value = NULL;

					/*
					 * Note that pg_get_one_r() replaces NULL values with
					 * the NA value appropriate for the data type.
					 */
					pg_get_one_r(value, element_type, &result, idx);
					if (value != NULL)
						pfree(value);
				}
			}
		}
		pfree(elem_values);
		pfree(elem_nulls);

		if (ndim > 1)
		{
			SEXP	matrix_dims;

			/* attach dimensions */
			PROTECT(matrix_dims = allocVector(INTSXP, ndim));
			for (i = 0; i < ndim; i++)
				INTEGER_DATA(matrix_dims)[i] = dim[i];

			setAttrib(result, R_DimSymbol, matrix_dims);
			UNPROTECT(1);
		}

		UNPROTECT(1);	/* result */
	}

	return result;
}

#ifdef HAVE_WINDOW_FUNCTIONS
/*
 * Evaluate a window function's argument expression on a specified
 *		window frame, returning R array for the argno column in the frame
 *
 * winobj: PostgreSQL window object handle
 * argno: argument number to evaluate (counted from 0)
 * function: contains necessary info on how to output Datum as string for general case conversion
 */
SEXP
pg_window_frame_get_r(WindowObject winobj, int argno, plr_function* function)
{
	/*
	 * Loop through and convert each scalar value.
	 * Use the converted values to build an R vector.
	 */
	SEXP		result;
	int			numels = 0;
	Oid			element_type = function->arg_typid[argno];
	FmgrInfo	out_func = function->arg_out_func[argno];
	int64		totalrows = WinGetPartitionRowCount(winobj);

	/*
	 * Get new vector of the appropriate type.
	 * We presume unbound frame as a common use case in R.
	 * If not, we will trim vector later.
	 */
	PROTECT(result = get_r_vector(element_type, totalrows));

	/* Convert all values to their R form and build the vector */
	for (;; numels++)
	{
		char	   *value;
		bool		isnull;
		Datum		dvalue;
		bool		isout = false;
		bool		set_mark = (0 == numels);

		dvalue = WinGetFuncArgInFrame(winobj, argno, numels, WINDOW_SEEK_HEAD,
			set_mark, &isnull, &isout);

		if (isout)
			break;

		switch (element_type)
		{
			case BOOLOID:
				LOGICAL_DATA(result)[numels] = isnull ? NA_LOGICAL : DatumGetBool(dvalue);
				break;
			case INT8OID:
				NUMERIC_DATA(result)[numels] = isnull ? NA_REAL : (double)DatumGetInt64(dvalue);
				break;
			case INT2OID:
			case INT4OID:
			case OIDOID:
				INTEGER_DATA(result)[numels] = isnull ? NA_INTEGER : DatumGetInt32(dvalue);
				break;
			case FLOAT4OID:
				NUMERIC_DATA(result)[numels] = isnull ? NA_REAL : DatumGetFloat4(dvalue);
				break;
			case FLOAT8OID:
				NUMERIC_DATA(result)[numels] = isnull ? NA_REAL : DatumGetFloat8(dvalue);
				break;
			default:
				value = isnull ? NULL : DatumGetCString(FunctionCall3(&out_func,
															dvalue,
															(Datum) 0,
															Int32GetDatum(-1)));

				/*
					* Note that pg_get_one_r() replaces NULL values with
					* the NA value appropriate for the data type.
					*/
				pg_get_one_r(value, element_type, &result, numels);
				if (value != NULL)
					pfree(value);
		}
	}

	if (numels != totalrows)
		SET_LENGTH(result, numels);

	UNPROTECT(1);	/* result */

	return result;
}
#endif

/*
 * Given an array of pg tuples, convert to an R list
 * the created object is not quite actually a data.frame
 */
SEXP
pg_tuple_get_r_frame(int ntuples, HeapTuple *tuples, TupleDesc tupdesc)
{
	int			nr = ntuples;
	int			nc = tupdesc->natts;
	int			nc_non_dropped = 0;
	int			df_colnum = 0;
	int			i = 0;
	int			j = 0;
	Oid			element_type;
	Oid			typelem;
	SEXP		names;
	SEXP		row_names;
	char		buf[256];
	SEXP		result;
	SEXP		fldvec;

	if (tuples == NULL || ntuples < 1)
		return R_NilValue;

	/* Count non-dropped attributes so we can later ignore the dropped ones */
	for (j = 0; j < nc; j++)
	{
		if (!TUPLE_DESC_ATTR(tupdesc,i)->attisdropped)
			nc_non_dropped++;
	}

	/*
	 * Allocate the data.frame initially as a list,
	 * and also allocate a names vector for the column names
	 */
	PROTECT(result = NEW_LIST(nc_non_dropped));
	PROTECT(names = NEW_CHARACTER(nc_non_dropped));

	/*
	 * Loop by columns
	 */
	for (j = 0; j < nc; j++)		
	{
		int16		typlen;
		bool		typbyval;
		char		typdelim;
		Oid			typoutput,
					typioparam;
		FmgrInfo	outputproc;
		char		typalign;

		/* ignore dropped attributes */
		if (TUPLE_DESC_ATTR(tupdesc,j)->attisdropped)
			continue;

		/* set column name */
		SET_COLUMN_NAMES;

		/* get column datatype oid */
		element_type = SPI_gettypeid(tupdesc, j + 1);

		/*
		 * Check to see if it is an array type. get_element_type will return
		 * InvalidOid instead of actual element type if the type is not a
		 * varlena array.
		 */
		typelem = get_element_type(element_type);

		/* get new vector of the appropriate type and length */
		if (typelem == InvalidOid)
			PROTECT(fldvec = get_r_vector(element_type, nr));
		else
		{
			PROTECT(fldvec = NEW_LIST(nr));
			get_type_io_data(typelem, IOFunc_output, &typlen, &typbyval,
							 &typalign, &typdelim, &typioparam, &typoutput);

			fmgr_info(typoutput, &outputproc);
		}

		/* loop rows for this column */
		for (i = 0; i < nr; i++)
		{
			if (typelem == InvalidOid)
			{
				/* not an array type */
				char	   *value;

				value = SPI_getvalue(tuples[i], tupdesc, j + 1);
				pg_get_one_r(value, element_type, &fldvec, i);
			}
			else
			{
				/* array type */
				Datum		dvalue;
				bool		isnull;
				SEXP		fldvec_elem;

				dvalue = SPI_getbinval(tuples[i], tupdesc, j + 1, &isnull);
				if (!isnull)
					PROTECT(fldvec_elem = pg_array_get_r(dvalue, outputproc, typlen, typbyval, typalign));
				else
					PROTECT(fldvec_elem = R_NilValue);

				SET_VECTOR_ELT(fldvec, i, fldvec_elem);
				UNPROTECT(1);
			}
		}

		SET_VECTOR_ELT(result, df_colnum, fldvec);
		UNPROTECT(1);
		df_colnum++;
	}

	/* attach the column names */
	setAttrib(result, R_NamesSymbol, names);

	/* attach row names - basically just the row number, zero based */
	PROTECT(row_names = allocVector(STRSXP, nr));
	for (i=0; i<nr; i++)
	{
		sprintf(buf, "%d", i+1);
		SET_STRING_ELT(row_names, i, COPY_TO_USER_STRING(buf));
	}
	setAttrib(result, R_RowNamesSymbol, row_names);

	/* finally, tell R we are a data.frame */
	setAttrib(result, R_ClassSymbol, mkString("data.frame"));

	UNPROTECT(3);
	return result;
}

/*
 * create an R vector of a given type and size based on pg output function oid
 */
static SEXP
get_r_vector(Oid typtype, int64 numels)
{
	SEXP	result;

	switch (typtype)
	{
		case OIDOID:
		case INT2OID:
		case INT4OID:
			/* 2 and 4 byte integer pgsql datatype => use R INTEGER */
			PROTECT(result = NEW_INTEGER(numels));
			break;
		case INT8OID:
		case FLOAT4OID:
		case FLOAT8OID:
		case CASHOID:
		case NUMERICOID:
			/*
			 * Other numeric types => use R REAL
			 * Note pgsql int8 is mapped to R REAL
			 * because R INTEGER is only 4 byte
			 */
			PROTECT(result = NEW_NUMERIC(numels));
			break;
		case BOOLOID:
			PROTECT(result = NEW_LOGICAL(numels));
			break;
		case BYTEAOID:
			PROTECT(result = NEW_RAW(numels));
			break;
		default:
			/* Everything else is defaulted to string */
			PROTECT(result = NEW_CHARACTER(numels));
	}
	UNPROTECT(1);

	return result;
}

/*
 * given a single non-array pg value, convert to its R value representation
 */
static void
pg_get_one_r(char *value, Oid typtype, SEXP *obj, int elnum)
{
	switch (typtype)
	{
		case OIDOID:
		case INT2OID:
		case INT4OID:
			/* 2 and 4 byte integer pgsql datatype => use R INTEGER */
			if (value)
				INTEGER_DATA(*obj)[elnum] = atoi(value);
			else
				INTEGER_DATA(*obj)[elnum] = NA_INTEGER;
			break;
		case INT8OID:
		case FLOAT4OID:
		case FLOAT8OID:
		case CASHOID:
		case NUMERICOID:
			/*
			 * Other numeric types => use R REAL
			 * Note pgsql int8 is mapped to R REAL
			 * because R INTEGER is only 4 byte
			 */
			if (value)
			{
				/* fixup for Visual Studio 2013, _MSC_VER == 1916*/
				char *endptr = NULL;
				const double el = strtod(value, &endptr);
				NUMERIC_DATA(*obj)[elnum] = value==endptr ? R_NaN : el;
			}
			else
				NUMERIC_DATA(*obj)[elnum] = NA_REAL;
			break;
		case BOOLOID:
			if (value)
				LOGICAL_DATA(*obj)[elnum] = ((*value == 't') ? 1 : 0);
			else
				LOGICAL_DATA(*obj)[elnum] = NA_LOGICAL;
			break;
		default:
			/* Everything else is defaulted to string */
			if (value)
				SET_STRING_ELT(*obj, elnum, COPY_TO_USER_STRING(value));
			else
				SET_STRING_ELT(*obj, elnum, NA_STRING);
	}
}

/*
 * given an R value, convert to its pg representation
 */
Datum
r_get_pg(SEXP rval, plr_result *result, FunctionCallInfo fcinfo)
{
	bool	isnull = false;
	Datum	dvalue;

	if (CALLED_AS_TRIGGER(fcinfo))
		dvalue = get_trigger_tuple(rval, fcinfo, &isnull);
	else if (fcinfo->flinfo->fn_retset)
		return get_tuplestore(rval, result, fcinfo);
	else if (result->natts > 1)
		return r_get_tuple(rval, result, fcinfo);
	else
		dvalue = get_datum(rval, result, 0, &isnull);

	if (isnull)
		fcinfo->isnull = true;

	return dvalue;
}

/*
 * Given an R value (data frame or list), coerce it to list
 * and get a tuple representing first elements of each list element.
 *
 * This is used to return a single RECORD (not SETOF)
 */
Datum
r_get_tuple(SEXP rval, plr_result *result, FunctionCallInfo fcinfo)
{
	Oid			oid;
	TupleDesc	tupdesc;
	HeapTuple	tuple;
	Datum	   *values;
	bool	   *isnull;
	int			i, min_length;

	if (!(isFrame(rval) || isNewList(rval) || isList(rval)))
		elog(ERROR, "Only list alike is expected");

	if (TYPEFUNC_COMPOSITE != get_call_result_type(fcinfo, &oid, &tupdesc))
		elog(ERROR, "return type must be a row type");

	min_length = Min(result->natts, length(rval));

	//if (tupdesc->natts != length(rval))
	//	elog(ERROR, "same length expected");

	BlessTupleDesc(tupdesc);

	values = palloc0(sizeof(Datum) * tupdesc->natts);
	isnull = palloc0(sizeof(bool) * tupdesc->natts);

	for (i = 0; i < min_length; i++)
	{
		SEXP el = VECTOR_ELT(rval, i);

		if (result->typid[i] == result->elem_typid[i])
		{
			result->get_datum[i] = get_mapper(TYPEOF(el), result->elem_typid[i]);
			values[i] = get_scalar_datum(el, result, i, isnull + i, 0);
		}
		else
			values[i] = get_array_datum(el, result, i);
	}

	tuple = heap_form_tuple(tupdesc, values, isnull);
	pfree(values);
	pfree(isnull);
	return HeapTupleGetDatum(tuple);
}

/*
 * Given an R value, convert to its pg representation
 * for non-SRF and non-composite types
 */
Datum
get_datum(SEXP rval, plr_result *result, int col, bool *isnull)
{
	Datum	dvalue;

	/* short circuit if return value is Null */
	if (rval == R_NilValue || isNull(rval))	/* probably redundant */
	{
		*isnull = true;
		return (Datum) 0;
	}


	if (result->elem_typid[col] == result->typid[col])
	{
		result->get_datum[col] = get_mapper(TYPEOF(rval), result->elem_typid[col]);
		dvalue = get_scalar_datum(rval, result, col, isnull, 0);
	}
	else
		dvalue = get_array_datum(rval, result, col);

	return dvalue;
}

static Datum
get_trigger_tuple(SEXP rval, FunctionCallInfo fcinfo, bool *isnull)
{
	TriggerData	   *trigdata = (TriggerData *) fcinfo->context;
	TupleDesc		tupdesc = trigdata->tg_relation->rd_att;
	AttInMetadata  *attinmeta;
	MemoryContext	fn_mcxt;
	MemoryContext	oldcontext;
	int				nc;
	int				nr;
	char		  **values;
	HeapTuple		tuple = NULL;
	int				i, j;
	int				nc_dropped = 0;
	int				df_colnum = 0;
	SEXP			result;
	SEXP			dfcol;

	/* short circuit statement level trigger which always returns NULL */
	if (TRIGGER_FIRED_FOR_STATEMENT(trigdata->tg_event))
	{
		/* special for triggers, don't set isnull flag */
		*isnull = false;
		return (Datum) 0;
	}

	/* short circuit if return value is Null */
	if (rval == R_NilValue || isNull(rval))	/* probably redundant */
	{
		/* special for triggers, don't set isnull flag */
		*isnull = false;
		return (Datum) 0;
	}

	if (isFrame(rval))
		nc = length(rval);
	else if (isMatrix(rval))
		nc = ncols(rval);
	else
		nc = 1;

	PROTECT(dfcol = VECTOR_ELT(rval, 0));
	nr = length(dfcol);
	UNPROTECT(1);

	if (nr != 1)
		ereport(ERROR,
				(errcode(ERRCODE_DATA_EXCEPTION),
				 errmsg("incorrect function return type"),
				 errdetail("function return value cannot have more " \
						   "than one row")));

	/*
	 * Count number of dropped attributes so we can add them back to
	 * the return tuple
	 */
	for (j = 0; j < nc; j++)
	{
		if (TUPLE_DESC_ATTR(tupdesc,j)->attisdropped)
			nc_dropped++;
	}

	/*
	 * Check to make sure we have the same number of columns
	 * to return as there are attributes in the return tuple.
	 * Note that we have to account for the number of dropped
	 * columns.
	 *
	 * Note we will attempt to coerce the R values into whatever
	 * the return attribute type is and depend on the "in"
	 * function to complain if needed.
	 */
	if (nc + nc_dropped != tupdesc->natts)
		ereport(ERROR,
				(errcode(ERRCODE_DATATYPE_MISMATCH),
				 errmsg("returned tuple structure does not match table " \
						"of trigger event")));

	fn_mcxt = fcinfo->flinfo->fn_mcxt;
	oldcontext = MemoryContextSwitchTo(fn_mcxt);

	attinmeta = TupleDescGetAttInMetadata(tupdesc);

	/* coerce columns to character in advance */
	PROTECT(result = NEW_LIST(nc));
	for (j = 0; j < nc; j++)
	{
		PROTECT(dfcol = VECTOR_ELT(rval, j));
		if(!isFactor(dfcol))
		{
			SEXP	obj;

			PROTECT(obj = coerce_to_char(dfcol));
			SET_VECTOR_ELT(result, j, obj);
			UNPROTECT(1);
		}
		else
		{
			SEXP 	t;

			for (t = ATTRIB(dfcol); t != R_NilValue; t = CDR(t))
			{
				if(TAG(t) == R_LevelsSymbol)
				{
					PROTECT(SETCAR(t, coerce_to_char(CAR(t))));
					UNPROTECT(1);
					break;
				}
			}
			SET_VECTOR_ELT(result, j, dfcol);
		}

		UNPROTECT(1);
	}

	values = (char **) palloc((nc + nc_dropped) * sizeof(char *));
	for(i = 0; i < nr; i++)
	{
		for (j = 0; j < nc + nc_dropped; j++)
		{
			/* insert NULL for dropped attributes */
			if (TUPLE_DESC_ATTR(tupdesc,j)->attisdropped)
				values[j] = NULL;
			else
			{
				PROTECT(dfcol = VECTOR_ELT(result, df_colnum));

				if(isFactor(dfcol))
				{
					SEXP t;
					for (t = ATTRIB(dfcol); t != R_NilValue; t = CDR(t))
					{
						if(TAG(t) == R_LevelsSymbol)
						{
							SEXP	obj;
							int		idx = INTEGER(dfcol)[i] - 1;

							PROTECT(obj = CAR(t));
							values[j] = pstrdup(CHAR(STRING_ELT(obj, idx)));
							UNPROTECT(1);

							break;
						}
					}
				}
				else
				{
					if (STRING_ELT(dfcol, 0) != NA_STRING)
						values[j] = pstrdup(CHAR(STRING_ELT(dfcol, i)));
					else
						values[j] = NULL;
				}

				UNPROTECT(1);
				df_colnum++;
			}
		}

		/* construct the tuple */
		tuple = BuildTupleFromCStrings(attinmeta, values);

		for (j = 0; j < nc; j++)
			if (values[j] != NULL)
				pfree(values[j]);
	}
	UNPROTECT(1);
	MemoryContextSwitchTo(oldcontext);

	if (tuple)
	{
		*isnull = false;
		return PointerGetDatum(tuple);
	}
	else
	{
		/* special for triggers, don't set isnull flag */
		*isnull = false;
		return (Datum) 0;
	}
}

static Datum
get_tuplestore(SEXP rval, plr_result *result, FunctionCallInfo fcinfo)
{
	ReturnSetInfo	   *rsinfo = (ReturnSetInfo *) fcinfo->resultinfo;
	Tuplestorestate	   *tupstore;
	TupleDesc			tupdesc;
	MemoryContext		per_query_ctx;
	MemoryContext		oldcontext;

	/* check to see if caller supports us returning a tuplestore */
	if (!rsinfo || !(rsinfo->allowedModes & SFRM_Materialize))
		ereport(ERROR,
				(errcode(ERRCODE_SYNTAX_ERROR),
				 errmsg("materialize mode required, but it is not "
						"allowed in this context")));

	per_query_ctx = rsinfo->econtext->ecxt_per_query_memory;
	oldcontext = MemoryContextSwitchTo(per_query_ctx);

	/* get the requested return tuple description */
	tupdesc = CreateTupleDescCopy(rsinfo->expectedDesc);

	/* initialize our tuplestore */
	tupstore = TUPLESTORE_BEGIN_HEAP;

	MemoryContextSwitchTo(oldcontext);

	/* OK, go to work */
	rsinfo->returnMode = SFRM_Materialize;
	rsinfo->setResult = tupstore;
	rsinfo->setDesc = tupdesc;
	get_tuplestore_imp(rval, result, tupdesc, tupstore);

	/*
	 * SFRM_Materialize mode expects us to return a NULL Datum. The actual
	 * tuples are in our tuplestore and passed back through
	 * rsinfo->setResult. rsinfo->setDesc is set to the tuple description
	 * that we actually used to build our tuples with, so the caller can
	 * verify we did what it was expecting.
	 */

	PG_RETURN_NULL();
}

Datum
intsxp_get_int2(SEXP rval, int idx, FmgrInfo *pg_restrict result_in_func, bool *pg_restrict isnull)
{
	const int el = INTEGER_ELT(rval, idx);
	*isnull = NA_INTEGER == el;
	return Int16GetDatum((int16)el);
}

Datum
intsxp_get_int4(SEXP rval, int idx, FmgrInfo *pg_restrict result_in_func, bool *pg_restrict isnull)
{
	const int el = INTEGER_ELT(rval, idx);
	*isnull = NA_INTEGER == el;
	return Int32GetDatum(el);
}

Datum
realsxp_get_float4(SEXP rval, int idx, FmgrInfo *pg_restrict result_in_func, bool *pg_restrict isnull)
{
	const double el = REAL_ELT(rval, idx);
	*isnull = ISNA(el);
	return Float4GetDatum((float4)el);
}

Datum
realsxp_get_float8(SEXP rval, int idx, FmgrInfo *pg_restrict result_in_func, bool *pg_restrict isnull)
{
	const double el = REAL_ELT(rval, idx);
	*isnull = ISNA(el);
	return Float8GetDatum(el);
}

Datum
realsxp_get_int8(SEXP rval, int idx, FmgrInfo *pg_restrict result_in_func, bool *pg_restrict isnull)
{
	const double el = REAL_ELT(rval, idx);
	*isnull = ISNA(el);
	return Int64GetDatum((int64)el);
}

Datum
realsxp_get_numeric(SEXP rval, int idx, FmgrInfo *pg_restrict result_in_func, bool *pg_restrict isnull)
{
	const double el = REAL_ELT(rval, idx);
	*isnull = ISNA(el);
	return DirectFunctionCall1(float8_numeric, Float8GetDatum((double)el));
}

Datum
get_bytea(SEXP rval, int idx, FmgrInfo *pg_restrict result_in_func, bool *pg_restrict isnull)
{
	SEXP		obj;
	int			len, rsize, status;
	bytea	   *result;
	char	   *rptr;
	const char *value = NULL;

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

get_datum_type
get_mapper(int sxp_type, Oid typid)
{
	switch (typid)
	{
		case BOOLOID:
		case INT4OID:
			switch (sxp_type)
			{
				case LGLSXP:
				case INTSXP:
					return intsxp_get_int4;
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
					return intsxp_get_int2;
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
					return realsxp_get_float8;
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

Datum
get_scalar_datum(SEXP rval, plr_result *result, int col, bool *isnull, int idx)
{
	/*
	 * passing a null into something like
	 * return as.real(NULL) will return numeric(0)
	 * which has a length of 0
	 */
	if (isNumeric(rval) && length(rval) == 0)
	{
		*isnull = true;
		return (Datum)0;
	}

	Assert(result->get_datum[col]);

	return (*result->get_datum[col]) (rval, idx, result->elem_in_func + col, isnull);
}

static Datum
get_array_datum(SEXP rval, plr_result *result, int col)
{
	if (isFrame(rval))
		return get_frame_array_datum(rval, result, col);

	result->get_datum[col] = get_mapper(TYPEOF(rval), result->elem_typid[col]);

	return get_md_array_datum(rval, result, col);
}

static inline Datum
get_scalar_datum_through_text(SEXP rval, int idx, FmgrInfo *pg_restrict result_in_func, bool *pg_restrict isnull)
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

static Datum
get_frame_array_datum(SEXP rval, plr_result *result, int col)
{
	Datum		dvalue;
	int			i;
	Datum	   *dvalues = NULL;
	ArrayType  *array;
	int			nr = 0;
	int			nc = length(rval);
#define FIXED_NUM_DIMS		2
	int			ndims = FIXED_NUM_DIMS;
	int			dims[FIXED_NUM_DIMS];
	int			lbs[FIXED_NUM_DIMS];
#undef FIXED_NUM_DIMS
	int			idx;
	SEXP		dfcol = NULL;
	int			j;
	bool	   *nulls = NULL;
	//get_datum_type mapper = get_mapper(TYPEOF(rval), result->elem_typid[col]);

	//Assert(result->get_datum[col]);

	if (nc < 1)
		/* internal error */
		elog(ERROR, "plr: bad internal representation of data.frame");

	for (j = 0; j < nc; j++)
	{
		PROTECT(dfcol = VECTOR_ELT(rval, j));
		result->get_datum[col] = get_mapper(TYPEOF(dfcol), result->elem_typid[col]);

		if (j == 0)
		{
			nr = length(dfcol);
			dvalues = (Datum *) palloc(nr * nc * sizeof(Datum));
			nulls = (bool *) palloc(nr * nc * sizeof(bool));
		}

		for(i = 0; i < nr; i++)
		{
			idx = ((i * nc) + j);
			dvalues[idx] = (*result->get_datum[col]) (dfcol, i, result->elem_in_func + col, nulls + idx);
		}
		UNPROTECT(1);
	}

	dims[0] = nr;
	dims[1] = nc;
	lbs[0] = 1;
	lbs[1] = 1;

	array = construct_md_array(dvalues, nulls, ndims, dims, lbs,
							   result->elem_typid[col], result->elem_typlen[col],
							   result->elem_typbyval[col], result->elem_typalign[col]);

	dvalue = PointerGetDatum(array);

	return dvalue;
}

static Datum
get_md_array_datum(SEXP rval, plr_result *result, int col)
{
	Datum		dvalue;
	SEXP		rdims;
	int			i, j;
	int			cardinality = length(rval);
	Datum	   *dvalues = NULL;
	ArrayType  *array;
	int		   *dims;
	int		   *lbs;
	int		   *cumprod;
	int		   *cumprod2;
	int		   *subs;
	int			idx;
	bool	   *nulls;
	int			ndims;
	FmgrInfo	in_func = result->elem_in_func[col];
	get_datum_type mapper = result->get_datum[col];

	Assert(result->get_datum[col]);

	PROTECT(rdims = GET_DIM(rval));
	ndims = length(rdims);
	if (ndims == 0)
		ndims = 1;
	cumprod = palloc((ndims + 1) * sizeof(int)); /* first is always 1, last is always cardinality */
	cumprod2 = palloc((ndims + 1) * sizeof(int)); /* first is always 1, last is always cardinality */
	if (ndims > 0)
	{
		dims = palloc(ndims * sizeof(int));
		lbs = palloc(ndims * sizeof(int));
		subs = palloc(ndims * sizeof(int));
		cumprod[0] = 1;
		cumprod2[0] = 1;
		if (!isNull(rdims)) /* matrix, array */
			for (i = 0; i < ndims; i++)
			{
				dims[i] = INTEGER_ELT(rdims, i);
				cumprod[i + 1] = cumprod[i] * dims[i];
				cumprod2[i + 1] = cumprod2[i] * INTEGER_ELT(rdims, ndims - i - 1);
				lbs[i] = 1;
			}
		else /* plain vector */
		{
			lbs[0] = 1;
			dims[0] = cardinality;
			cumprod[1] = cardinality;
			cumprod2[1] = 1;
		}
	}
	else
	{
		dims = NULL;
		lbs = NULL;
	}
	UNPROTECT(1);

	dvalues = (Datum *) palloc(cardinality * sizeof(Datum));
	nulls = (bool *) palloc(cardinality * sizeof(bool));

	for (i = 0; i < cardinality; i++)
	{
		/* Convert linear index from fast last to fast first subscript
		 * through mixed radix conversion, subscripts order flip,
		 * and conversion back from mixed radix to linear index using dot product  */
		idx = i;
		for (j = 0; j < ndims; j++)
		{
			const int tmp = cumprod2[ndims - j - 1];
			subs[j] = idx / tmp;
			idx %= tmp;
		}
		// Assert(idx == 0);
		for (j = 0; j < ndims; j++)
			idx += subs[j] * cumprod[j];

		dvalues[i] = (*mapper) (rval, idx, &in_func, &nulls[i]);
	}

	array = construct_md_array(dvalues, nulls, ndims, dims, lbs,
							   result->elem_typid[col], result->elem_typlen[col],
							   result->elem_typbyval[col], result->elem_typalign[col]);

	dvalue = PointerGetDatum(array);

	pfree(cumprod);
	pfree(cumprod2);
	pfree(dims);
	pfree(lbs);
	pfree(subs);
	pfree(dvalues);
	pfree(nulls);

	return dvalue;
}

static void
get_tuplestore_imp(SEXP rval,
					 plr_result *result,
					 TupleDesc tupdesc,
					 Tuplestorestate *tupstore)
{
	Datum			   *values;
	bool			   *isnull;
	int					tupdesc_nc = tupdesc->natts;
	int					i, j, idx;
	int					nr;
	int					nc;
	SEXP				dim, el;
	int					dim_length, status;
	SEXP				t, args;
	int					is_frame = isFrame(rval);

	if (is_frame)
	{
		nc = length(rval);
		PROTECT(el = VECTOR_ELT(rval, 0));
		nr = length(el);
		UNPROTECT(1);
	}
	else
	{
		dim = GET_DIM(rval);
		dim_length = length(dim);
		if (dim_length > 0)
			nr = INTEGER_ELT(dim, 0);
		if (dim_length > 1)
			nc = INTEGER_ELT(dim, 1);
		else
			nc = 1;
		if (dim_length == 0)
		{
			nr = length(rval);
			dim_length = 1;
		}

		if (dim_length > 2)
		{
			/* prepare for rval[i,j,...] subsetting */
			t = args = PROTECT(allocList(dim_length + 2));
			SET_TYPEOF(args, LANGSXP);
			SETCAR(t, R_BracketSymbol); t = CDR(t);
			SETCAR(t, rval); t = CDR(t);
			for (i = 0; i < dim_length; i++, t = CDR(t))
				SETCAR(t, R_MissingArg);
			t = CDDR(args);
		} /* otherwise we can tap into corresponding element directly */
	}

	if (nc != tupdesc_nc)
		ereport(ERROR,
		(errcode(ERRCODE_DATA_EXCEPTION),
			errmsg("actual and requested return type mismatch"),
			errdetail("Actual return type has %d columns, but " \
					  "requested return type has %d", nc, tupdesc_nc)));

	values = palloc0(sizeof(Datum) * tupdesc_nc);
	isnull = palloc0(sizeof(bool) * tupdesc_nc);

	for (j = 0; j < nc; j++)
	{
		if (is_frame)
			el = VECTOR_ELT(rval, j);
		else
			el = rval;
		result->get_datum[j] = get_mapper(TYPEOF(el), result->elem_typid[j]);
	}

	for(i = 0; i < nr; i++)
	{
		for (j = 0; j < nc; j++)
		{
			if (likely(is_frame))
			{
				PROTECT(el = VECTOR_ELT(rval, j));
				idx = i;
			}
			else if (dim_length <= 2) /* matrix and array up to 2D */
			{
				PROTECT(el = rval);
				idx = i + nr * j;
			}
			else
			{
				/* worst case as we need to subset from within R and request new data_ptr */
				SETCAR(t, ScalarInteger(i + 1));
				SETCADR(t, ScalarInteger(j + 1));
				PROTECT(el = R_tryEval(args, R_GlobalEnv, &status));
				result->data_ptr[j] = STDVEC_DATAPTR(el);
				/* we expect PG array */
				Assert(result->typid[j] != result->elem_typid[j]);

				if (unlikely(status))
					elog(ERROR, "Failed to get subscript");
			}

			if (likely(result->typid[j] == result->elem_typid[j]))
				values[j] = get_scalar_datum(el,
											 result, j,
											 isnull + j,
											 idx);
			else
				values[j] = get_md_array_datum(el, result, j);

			UNPROTECT(1);
		}

		/* Context is switched internally */
		tuplestore_putvalues(tupstore, tupdesc, values, isnull);
	}

	if (!is_frame && dim_length > 2)
		UNPROTECT(1); /* rval[i,j,...] call */

	pfree(values);
	pfree(isnull);
}

static SEXP
coerce_to_char(SEXP rval)
{
	SEXP	obj = NULL;

	switch (TYPEOF(rval))
	{
		case LISTSXP:
		case NILSXP:
		case SYMSXP:
		case VECSXP:
		case EXPRSXP:
		case LGLSXP:
		case INTSXP:
		case REALSXP:
		case CPLXSXP:
		case STRSXP:
		case RAWSXP:
			PROTECT(obj = AS_CHARACTER(rval));
			break;
		default:
			ereport(ERROR,
			(errcode(ERRCODE_DATA_EXCEPTION),
				errmsg("data type coercion error"),
				errdetail("R object is not an expected " \
						  "data type; examine your R code")));
	}
	UNPROTECT(1);

	return obj;
}
