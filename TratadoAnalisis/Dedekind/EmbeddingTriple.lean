import TratadoAnalisis.Foundations.FunctionTriple
import TratadoAnalisis.Dedekind.Embedding

namespace TratadoAnalisis.Dedekind.EmbeddingTriple
universe u
open TratadoAnalisis.Foundations.FunctionTriple
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Embedding

/-- El objeto conjuntista ι_D, incluido su dominio y codominio. -/
def dedekindEmbeddingFunction : ZFSet.{u} :=
  functionTriple rationalsTA dedekindCutsTA dedekindEmbeddingGraph

/-- TA-DEF-00084: cierre del certificado como triple, sin editar Embedding. -/
theorem TA_DEF_00084_embeddingFunction_isTriple :
    IsFunctionTriple (rationalsTA : ZFSet.{u}) dedekindCutsTA
      dedekindEmbeddingFunction :=
  TA_DEF_00018_functionTriple_iff.mpr TA_DEF_00084_embeddingGraph_isFunc

end TratadoAnalisis.Dedekind.EmbeddingTriple
