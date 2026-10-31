// Copyright (c) 2026 Microsoft Corporation
import java.lang.reflect.InvocationTargetException;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.channels.FileChannel;
import java.nio.channels.FileLock;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

/** Exercise the actual Native initializer in retained, isolated ClassLoaders. */
public final class CacheClassLoaderTest {
    private static void solve(URLClassLoader loader, String version) throws Exception {
        try {
            loader.loadClass("Smoke").getMethod("main", String[].class).invoke(null,
                (Object) new String[] {"lifecycle", version});
        } catch (InvocationTargetException ex) {
            throw new AssertionError("Isolated ClassLoader failed", ex.getCause());
        }
    }

    public static void main(String[] args) throws Exception {
        List<URLClassLoader> retained = new ArrayList<URLClassLoader>();
        FileChannel channel = null;
        FileLock lock = null;
        try {
            if (args[0].equals("overlap")) {
                channel = FileChannel.open(Paths.get(System.getProperty("z3.nativeCacheDir"), ".lock"),
                    StandardOpenOption.CREATE, StandardOpenOption.WRITE);
                lock = channel.lock();
            }
            for (int i = 0; i < (lock == null ? 2 : 1); i++) {
                URLClassLoader loader = new URLClassLoader(new URL[] {
                    Paths.get(args[1]).toUri().toURL(), Paths.get(args[2]).toUri().toURL()
                }, null);
                retained.add(loader);
            }
            if (args[0].equals("concurrent")) {
                ExecutorService executor = Executors.newFixedThreadPool(2);
                try {
                    List<Future<Void>> futures = new ArrayList<Future<Void>>();
                    for (URLClassLoader loader : retained) {
                        futures.add(executor.submit(() -> { solve(loader, args[3]); return null; }));
                    }
                    for (Future<Void> future : futures) { future.get(); }
                } finally {
                    executor.shutdownNow();
                }
            } else {
                for (URLClassLoader loader : retained) { solve(loader, args[3]); }
            }
            java.io.File[] extracted = new java.io.File(System.getProperty("java.io.tmpdir")).listFiles();
            if (extracted == null || extracted.length != 1 || !extracted[0].isDirectory()
                    || extracted[0].list().length != 2) {
                throw new AssertionError("Expected one private native pair for the ClassLoader fallback");
            }
            System.out.println("PASS " + args[0] + " ClassLoaders: " + retained.size());
        } finally {
            if (lock != null) { lock.release(); }
            if (channel != null) { channel.close(); }
            for (URLClassLoader loader : retained) { loader.close(); }
        }
    }
}
