/**
 * Provides modeling for the `ActiveStorage` library.
 */

private import codeql.ruby.AST
private import codeql.ruby.Concepts
private import codeql.ruby.DataFlow
private import codeql.ruby.dataflow.FlowSummary
private import codeql.ruby.frameworks.data.ModelsAsData
private import codeql.ruby.frameworks.ActiveRecord

/**
 * Provides modeling for the `ActiveStorage` library.
 * Version: 7.0.
 */
module ActiveStorage {
  /** A call to `ActiveStorage::Filename#sanitized`, considered as a path sanitizer. */
  private class FilenameSanitizedCall extends Path::PathSanitization::Range, DataFlow::CallNode {
    FilenameSanitizedCall() {
      this =
        DataFlow::getConstant("ActiveStorage").getConstant("Filename").getAMethodCall("sanitized")
    }
  }

  /** Taint related to `ActiveStorage::Filename`. */
  private class FilenameSummaries extends ModelInput::SummaryModelCsv {
    override predicate row(string row) {
      row =
        [
          "ActiveStorage::Filename!;Method[new];Argument[0];ReturnValue;taint",
          "ActiveStorage::Filename;Method[sanitized];Argument[self];ReturnValue;taint",
        ]
    }
  }

  /**
   * `Blob` is an instance of `ActiveStorage::Blob`.
   */
  private class BlobTypeSummary extends ModelInput::TypeModelCsv {
    override predicate row(string row) {
      // package1;type1;package2;type2;path
      row =
        [
          // ActiveStorage::Blob.create_and_upload! : Blob
          "ActiveStorage::Blob;ActiveStorage::Blob!;Method[create_and_upload!].ReturnValue",
          // ActiveStorage::Blob.create_before_direct_upload! : Blob
          "ActiveStorage::Blob;ActiveStorage::Blob!;Method[create_before_direct_upload!].ReturnValue",
          // ActiveStorage::Blob.compose(blobs : [Blob]) : Blob
          "ActiveStorage::Blob;ActiveStorage::Blob!;Method[compose].ReturnValue",
          // gives error: Invalid name 'Element' in access path
          // "ActiveStorage::Blob;ActiveStorage::Blob!;Method[compose].Argument[0].Element[any]",
          // ActiveStorage::Blob.find_signed(!) : Blob
          "ActiveStorage::Blob;ActiveStorage::Blob!;Method[find_signed,find_signed!].ReturnValue",
        ]
    }
  }

  private class BlobInstance extends DataFlow::LocalSourceNode {
    BlobInstance() {
      this = ModelOutput::getATypeNode("ActiveStorage::Blob").asSource()
      or
      // ActiveStorage::Attachment#blob : Blob
      this = any(AttachmentInstance i).getAMethodCall("blob")
      or
      // ActiveStorage::Attachment delegates method calls to its associated Blob
      this instanceof AttachmentInstance
    }
  }

  /**
   * Method calls on `ActiveStorage::Blob` that send HTTP requests.
   */
  private class BlobRequestCall extends Http::Client::Request::Range {
    BlobRequestCall() {
      this =
        [
          // Class methods
          DataFlow::getConstant("ActiveStorage")
              .getConstant("Blob")
              .getAMethodCall(["create_after_unfurling!", "create_and_upload!"]),
          // Instance methods
          any(BlobInstance i)
              .getAMethodCall([
                  "upload", "upload_without_unfurling", "download", "download_chunk", "delete",
                  "purge"
                ])
        ]
    }

    override string getFramework() { result = "activestorage" }

    override DataFlow::Node getResponseBody() { result = this }

    override DataFlow::Node getAUrlPart() { none() }

    override predicate disablesCertificateValidation(
      DataFlow::Node disablingNode, DataFlow::Node argumentOrigin
    ) {
      none()
    }
  }

  /**
   * A call to `has_one_attached` or `has_many_attached`, which declares an
   * association between an ActiveRecord model and an ActiveStorage attachment.
   *
   * ```rb
   * class User < ActiveRecord::Base
   *   has_one_attached :avatar
   * end
   * ```
   */
  private class Association extends ActiveRecordAssociation {
    Association() { this.getMethodName() = ["has_one_attached", "has_many_attached"] }
  }

  /**
   * An ActiveStorage attachment, instantiated directly or via an association with an
   * ActiveRecord model.
   *
   * ```rb
   * class User < ActiveRecord::Base
   *   has_one_attached :avatar
   * end
   *
   * user = User.find(id)
   * user.avatar
   * ActiveStorage::Attachment.new
   * ```
   */
  class AttachmentInstance extends DataFlow::LocalSourceNode {
    AttachmentInstance() {
      this = DataFlow::getConstant("ActiveStorage").getConstant("Attachment").getAMethodCall("new")
      or
      exists(ActiveRecordModelInstantiation record, Association assoc |
        record.getClass() = assoc.getSourceClass() and
        this = record.getAMethodCall(assoc.getTargetModelName())
      )
    }
  }

  /**
   * A call on an ActiveStorage object that results in an image transformation.
   * Arguments to these calls may be executed as system commands.
   */
  private class ImageProcessingCall extends SystemCommandExecution::Range instanceof DataFlow::CallNode
  {
    ImageProcessingCall() {
      this = any(BlobInstance i).getAMethodCall(["variant", "preview", "representation"])
      or
      this =
        DataFlow::getConstant("ActiveStorage")
            .getConstant("Attachment")
            .getAMethodCall("new")
            .getAMethodCall(["variant", "preview", "representation"])
      or
      this =
        DataFlow::getConstant("ActiveStorage")
            .getConstant("Variation")
            .getAMethodCall(["new", "wrap", "encode"])
      or
      this =
        DataFlow::getConstant("ActiveStorage")
            .getConstant("Variation")
            .getAMethodCall("new")
            .getAMethodCall("transformations=")
      or
      this =
        DataFlow::getConstant("ActiveStorage")
            .getConstant("Transformers")
            .getConstant("ImageProcessingTransformer")
            .getAMethodCall("new")
      or
      this =
        DataFlow::getConstant("ActiveStorage")
            .getConstant(["Preview", "VariantWithRecord"])
            .getAMethodCall("new")
      or
      // `ActiveStorage.paths` is a global hash whose values are passed to
      // a `system` call.
      this = DataFlow::getConstant("ActiveStorage").getAMethodCall("paths=")
      or
      // `ActiveStorage.video_preview_arguments` is passed to a `system` call.
      this = DataFlow::getConstant("ActiveStorage").getAMethodCall("video_preview_arguments=")
    }

    override DataFlow::Node getAnArgument() { result = super.getArgument(0) }
  }

  /**
   * `ActiveStorage.variant_processor` is passed to `const_get`.
   */
  private class VariantProcessor extends DataFlow::CallNode, CodeExecution::Range {
    VariantProcessor() {
      this = DataFlow::getConstant("ActiveStorage").getAMethodCall("variant_processor=")
    }

    override DataFlow::Node getCode() { result = this.getArgument(0) }

    override predicate runsArbitraryCode() { none() }
  }
}
