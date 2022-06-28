// tslint:disable
/**
 * Yugabyte Cloud
 * YugabyteDB as a Service
 *
 * The version of the OpenAPI document: v1
 * Contact: support@yugabyte.com
 *
 * NOTE: This class is auto generated by OpenAPI Generator (https://openapi-generator.tech).
 * https://openapi-generator.tech
 * Do not edit the class manually.
 */


// eslint-disable-next-line no-duplicate-imports
import type { AddressSpec } from './AddressSpec';
// eslint-disable-next-line no-duplicate-imports
import type { BillingTypeSpec } from './BillingTypeSpec';
// eslint-disable-next-line no-duplicate-imports
import type { PaymentMethodEnum } from './PaymentMethodEnum';


/**
 * Billing profile spec
 * @export
 * @interface BillingProfileSpec
 */
export interface BillingProfileSpec  {
  /**
   * 
   * @type {string}
   * @memberof BillingProfileSpec
   */
  contact_name: string;
  /**
   * 
   * @type {string}
   * @memberof BillingProfileSpec
   */
  contact_email_address: string;
  /**
   * 
   * @type {string}
   * @memberof BillingProfileSpec
   */
  contact_phone?: string;
  /**
   * 
   * @type {string}
   * @memberof BillingProfileSpec
   */
  company_name?: string;
  /**
   * 
   * @type {AddressSpec}
   * @memberof BillingProfileSpec
   */
  invoice_address: AddressSpec;
  /**
   * 
   * @type {AddressSpec}
   * @memberof BillingProfileSpec
   */
  billing_address: AddressSpec;
  /**
   * 
   * @type {string}
   * @memberof BillingProfileSpec
   */
  duns_number?: string;
  /**
   * 
   * @type {string}
   * @memberof BillingProfileSpec
   */
  tax_registration_number?: string;
  /**
   * 
   * @type {BillingTypeSpec}
   * @memberof BillingProfileSpec
   */
  billing_type?: BillingTypeSpec;
  /**
   * 
   * @type {string}
   * @memberof BillingProfileSpec
   */
  payment_method_id?: string;
  /**
   * 
   * @type {PaymentMethodEnum}
   * @memberof BillingProfileSpec
   */
  payment_method_type: PaymentMethodEnum;
}


