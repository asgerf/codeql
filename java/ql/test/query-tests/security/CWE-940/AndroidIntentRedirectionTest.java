package com.example.app;

import android.app.Activity;
import android.content.ComponentName;
import android.content.Context;
import android.content.Intent;
import android.os.Bundle;

public class AndroidIntentRedirectionTest extends Activity {

    public void onCreate(Bundle savedInstanceState) {
        Intent intent = (Intent) getIntent().getParcelableExtra("forward_intent");

        // @formatter:off
        startActivities(new Intent[] {intent}); // $ hasAndroidIntentRedirection
        startActivities(new Intent[] {intent}, null); // $ hasAndroidIntentRedirection
        startActivity(intent); // $ hasAndroidIntentRedirection
        startActivity(intent, null); // $ hasAndroidIntentRedirection
        startActivityAsUser(intent, null); // $ hasAndroidIntentRedirection
        startActivityAsUser(intent, null, null); // $ hasAndroidIntentRedirection
        startActivityAsCaller(intent, null, false, 0); // $ hasAndroidIntentRedirection
        startActivityForResult(intent, 0); // $ hasAndroidIntentRedirection
        startActivityForResult(intent, 0, null); // $ hasAndroidIntentRedirection
        startActivityForResult(null, intent, 0, null); // $ hasAndroidIntentRedirection
        startActivityForResultAsUser(intent, null, 0, null, null); // $ hasAndroidIntentRedirection
        startActivityForResultAsUser(intent, 0, null, null); // $ hasAndroidIntentRedirection
        startActivityForResultAsUser(intent, 0, null); // $ hasAndroidIntentRedirection
        startService(intent); // $ hasAndroidIntentRedirection
        startServiceAsUser(intent, null); // $ hasAndroidIntentRedirection
        sendBroadcast(intent); // $ hasAndroidIntentRedirection
        sendBroadcast(intent, null); // $ hasAndroidIntentRedirection
        sendBroadcast(intent, null, null); // $ hasAndroidIntentRedirection
        sendBroadcast(intent, null, 0); // $ hasAndroidIntentRedirection
        sendBroadcastAsUser(intent, null); // $ hasAndroidIntentRedirection
        sendBroadcastAsUser(intent, null, null); // $ hasAndroidIntentRedirection
        sendBroadcastAsUser(intent, null, null, null); // $ hasAndroidIntentRedirection
        sendBroadcastAsUser(intent, null, null, 0); // $ hasAndroidIntentRedirection
        sendBroadcastWithMultiplePermissions(intent, null); // $ hasAndroidIntentRedirection
        sendStickyBroadcast(intent); // $ hasAndroidIntentRedirection
        sendStickyBroadcastAsUser(intent, null); // $ hasAndroidIntentRedirection
        sendStickyBroadcastAsUser(intent, null, null); // $ hasAndroidIntentRedirection
        sendStickyOrderedBroadcast(intent, null, null, 0, null, null); // $ hasAndroidIntentRedirection
        sendStickyOrderedBroadcastAsUser(intent, null, null, null, 0, null, null); // $ hasAndroidIntentRedirection
        // @formatter:on

        if (intent.getComponent().getPackageName().equals("something")) {
            startActivity(intent); // Safe - sanitized
        } else {
            startActivity(intent); // $ hasAndroidIntentRedirection
        }
        if (intent.getComponent().getClassName().equals("something")) {
            startActivity(intent); // Safe - sanitized
        } else {
            startActivity(intent); // $ hasAndroidIntentRedirection
        }

        try {
            {
                // Delayed cast
                Object obj = getIntent().getParcelableExtra("forward_intent");
                Intent fwdIntent = (Intent) obj;
                startActivity(fwdIntent); // $ hasAndroidIntentRedirection
            }
            {
                Intent fwdIntent = new Intent();
                fwdIntent.setClassName((Context) null, (String) intent.getExtra("className"));
                startActivity(fwdIntent); // $ hasAndroidIntentRedirection
            }
            {
                Intent fwdIntent = new Intent();
                fwdIntent.setClassName((String) intent.getExtra("packageName"), null);
                startActivity(fwdIntent); // $ hasAndroidIntentRedirection
            }
            {
                Intent fwdIntent = new Intent();
                fwdIntent.setClassName((String) intent.getExtra("packageName"),
                        (String) intent.getExtra("className"));
                startActivity(fwdIntent); // $ hasAndroidIntentRedirection
            }
            {
                Intent fwdIntent = new Intent();
                fwdIntent.setClass(null, Class.forName((String) intent.getExtra("className")));
                // needs taint step for Class.forName
                startActivity(fwdIntent); // $ MISSING: $hasAndroidIntentRedirection
            }
            {
                Intent fwdIntent = new Intent();
                fwdIntent.setPackage((String) intent.getExtra("packageName"));
                startActivity(fwdIntent); // $ hasAndroidIntentRedirection
            }
            {
                Intent fwdIntent = new Intent();
                ComponentName component =
                        new ComponentName((String) intent.getExtra("packageName"), null);
                fwdIntent.setComponent(component);
                startActivity(fwdIntent); // $ hasAndroidIntentRedirection
            }
            {
                Intent fwdIntent = new Intent();
                ComponentName component =
                        new ComponentName("", (String) intent.getExtra("className"));
                fwdIntent.setComponent(component);
                startActivity(fwdIntent); // $ hasAndroidIntentRedirection
            }
            {
                Intent fwdIntent = new Intent();
                ComponentName component =
                        new ComponentName((Context) null, (String) intent.getExtra("className"));
                fwdIntent.setComponent(component);
                startActivity(fwdIntent); // $ hasAndroidIntentRedirection
            }
            {
                Intent fwdIntent = new Intent();
                ComponentName component = new ComponentName((Context) null,
                        Class.forName((String) intent.getExtra("className")));
                fwdIntent.setComponent(component);
                // needs taint step for Class.forName
                startActivity(fwdIntent); // $ MISSING: $hasAndroidIntentRedirection
            }
            {
                Intent fwdIntent = new Intent();
                ComponentName component =
                        ComponentName.createRelative("", (String) intent.getExtra("className"));
                fwdIntent.setComponent(component);
                startActivity(fwdIntent); // $ hasAndroidIntentRedirection
            }
            {
                Intent fwdIntent = new Intent();
                ComponentName component =
                        ComponentName.createRelative((String) intent.getExtra("packageName"), "");
                fwdIntent.setComponent(component);
                startActivity(fwdIntent); // $ hasAndroidIntentRedirection
            }
            {
                Intent fwdIntent = new Intent();
                ComponentName component = ComponentName.createRelative((Context) null,
                        (String) intent.getExtra("className"));
                fwdIntent.setComponent(component);
                startActivity(fwdIntent); // $ hasAndroidIntentRedirection
            }
            {
                Intent originalIntent = getIntent();
                ComponentName cp = new ComponentName(originalIntent.getStringExtra("packageName"),
                        originalIntent.getStringExtra("className"));
                Intent anotherIntent = new Intent();
                anotherIntent.setComponent(cp);
                startActivity(originalIntent); // Safe - not a tainted Intent
            }
            {
                Intent originalIntent = getIntent();
                Intent anotherIntent = new Intent(originalIntent);
                startActivity(anotherIntent); // Safe - copy constructor from original Intent
            }
            {
                Intent originalIntent = getIntent();
                Intent fwdIntent = (Intent) originalIntent.getParcelableExtra("forward_intent");
                if (originalIntent.getBooleanExtra("use_fwd_intent", false)) {
                    startActivity(fwdIntent); // $ hasAndroidIntentRedirection
                } else {
                    startActivity(originalIntent); // Safe - not an Intent obtained from the Extras
                }
            }
            {
                Intent originalIntent = getIntent();
                originalIntent.setClassName(originalIntent.getStringExtra("package_name"),
                        originalIntent.getStringExtra("class_name"));
                startActivity(originalIntent); // $ hasAndroidIntentRedirection
            }
            {
                Intent originalIntent = getIntent();
                originalIntent.setClassName("not_user_provided", "not_user_provided");
                startActivity(originalIntent); // Safe - component changed but not tainted
            }
            {
                Intent originalIntent = getIntent();
                Intent fwdIntent;
                if (originalIntent.getBooleanExtra("use_fwd_intent", false)) {
                    fwdIntent = (Intent) originalIntent.getParcelableExtra("forward_intent");
                } else {
                    fwdIntent = originalIntent;
                }
                // Conditionally tainted sinks aren't supported currently
                startActivity(fwdIntent); // $ MISSING: $hasAndroidIntentRedirection
            }
        } catch (Exception e) {
        }
    }
}
